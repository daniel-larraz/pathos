module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Embed
public import PathosProofs.Runtime.Builtins
public import PathosProofs.Runtime.Lists
public import PathosProofs.Runtime.StateInv
public import MiniCtors

/-!
# The assumption fold: `$eo_invoke_assume_list`

The generator compiles `$eo_invoke_assume_list` to an iterative fold
(Ethos `rust_meta_reduce.cpp`, "guarded right fold"): `scan` goes down the
list of assumptions, keeping each guard (`eo::and` of `$eo_is_bool_type`
and `$eo_is_closed`) with its formula, and `unwind` pushes them with
`$eo_push_input_assume_check` from the last to the first, as logos's
recursive definition does. Here that fold is proved against logos's
`__eo_invoke_assume_list`, from what is proved of the three programs it
calls (taken as hypotheses, in the shape of the generated specs).

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- What `$eo_is_bool_type` is to compute (the shape of a generated spec). -/
def IsBoolTypeSpec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : Eo.Term), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    generated.part0.eo__24eo_5fis_5fbool_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_is_bool_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What `$eo_is_closed` is proved to compute. -/
def IsClosedSpec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : Eo.Term), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    generated.part0.eo__24eo_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What `$eo_push_input_assume_check` is proved to compute. -/
def PushInputSpec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : Eo.Term) (x_a1 : Eo.Term) (x_a2 : Eo.CState),
    s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    StateOK x_a2 →
    generated.part0.eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_push_input_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- The guard of an assumption. -/
def assumeGuard (F : Eo.Term) : Eo.Term := Eo.__eo_and (Eo.__eo_is_bool_type F) (Eo.__eo_is_closed F)

/-- The formulas of a list of assumptions. -/
def cargs : Eo.CArgList → List Eo.Term
  | Eo.CArgList.nil => []
  | Eo.CArgList.cons F rest => F :: cargs rest

/-- logos's `__eo_invoke_assume_list` is a right fold of the guarded pushes. -/
theorem invoke_assume_list_foldr (S : Eo.CState) (xs : Eo.CArgList) :
    Eo.__eo_invoke_assume_list S xs =
      (cargs xs).foldr (fun F st => Eo.__eo_push_input_assume_check (assumeGuard F) F st) S := by
  induction xs with
  | nil => rfl
  | cons F rest ih => simp [Eo.__eo_invoke_assume_list, cargs, ih, assumeGuard]

/-- The fold's first case: the end of the list. -/
theorem fold_case0_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) (a0 a1 : Term)
    {x1 : Eo.CArgList} (h1 : Represents.rep s a1 x1) :
    generated.part0.case_0_eo__24eo_5finvoke_5fassume_5flist s a0 a1 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (FoldStep.Done t)) => x1 = Eo.CArgList.nil ∧ t = a0
      | core.result.Result.Ok (some (FoldStep.Push _ _ _)) => False
      | core.result.Result.Ok none => x1 ≠ Eo.CArgList.nil
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_0_eo__24eo_5finvoke_5fassume_5flist
  step as ⟨e, he⟩
  step with CtorSpec.eo__24emb_5fal_2enil.construct s e (by rw [he]; exact empty_args) hinv h64
    as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e =>
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv1, hg1, trivial⟩
  | Ok v =>
    simp only [term_ne] at *
    have h1' := Represents.grows h1 hg1
    have hiff := Represents.eq_iff hinv1 h1' hr
    by_cases hav : a1 = v
    · simp only [hav, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hiff.mp hav, trivial⟩
    · simp only [hav, decide_false, Bool.not_false, ite_true, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      exact ⟨hinv1, hg1, fun h => hav (hiff.mpr h)⟩

/-- `tick` keeps the invariant and grows the store. -/
theorem Store.tick_grows (s : Store) (hinv : s.Inv) :
    Store.tick s ⦃ r s' => s'.Inv ∧ s.Grows s' ⦄ := by
  apply WP.spec_mono (Store.tick_spec s)
  rintro ⟨r, s'⟩ ⟨hn, hh, hs, hc, hl, hd, hb, _⟩
  exact ⟨hinv.congr hn hh hs hc, ⟨by rw [hn], hl, hd, hb⟩⟩

/-- The fields that `destruct` gives are earlier handles. -/
theorem Store.destruct_fields_lt {s s' : Store} (hinv : s.Inv) {c : schema.Constructor}
    {t : Term} {v : alloc.vec.Vec Term}
    (hemb : c.embedding = ok Embedding.Data ∨ c.embedding = ok Embedding.Var)
    (hd : Store.destruct s c t = ok (core.result.Result.Ok (some v), s')) :
    ∀ x ∈ v.val, x.val < t.val := by
  rw [Store.destruct_data_eq s c t hemb] at hd
  by_cases hlt : t.val < s.nodes.length
  · simp only [hlt, ite_true] at hd
    have hwf := hinv.terms.wf t.val hlt
    unfold Store.data at hd
    cases hdt : s.nodes.val[t.val]! with
    | Node d fields =>
      rw [hdt] at hd hwf
      by_cases hdc : d = c
      · simp only [hdc, ite_true] at hd
        simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq, Option.some.injEq] at hd
        obtain ⟨rfl, _⟩ := hd
        obtain ⟨hf, _⟩ := hwf
        intro x hx
        have := hf x hx
        simp only [List.length_take] at this
        omega
      · simp [hdc] at hd
    | _ => rw [hdt] at hd; simp at hd
  · simp [hlt] at hd

/-- The fold's second case: an assumption, with its guard. -/
theorem fold_case1_spec (m : Nat) (hb : IsBoolTypeSpec m) (hc : IsClosedSpec m) (s : Store)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ m) (a0 a1 : Term)
    {x1 : Eo.CArgList} (h1 : Represents.rep s a1 x1) :
    generated.part0.case_1_eo__24eo_5finvoke_5fassume_5flist s a0 a1 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (FoldStep.Push g t tl)) =>
        ∃ F rest, x1 = Eo.CArgList.cons F rest ∧ Represents.rep s' g (assumeGuard F) ∧
          Represents.rep s' t F ∧ Represents.rep s' tl rest ∧ tl.val < a1.val
      | core.result.Result.Ok (some (FoldStep.Done _)) => False
      | core.result.Result.Ok none => ∀ F rest, x1 ≠ Eo.CArgList.cons F rest
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_1_eo__24eo_5finvoke_5fassume_5flist
  rcases CtorSpec.eo__24emb_5fal_2econs.destruct h1 with
    ⟨f0, f1, v, x0, xr, rfl, hv, hf0, hf1, hd⟩ | ⟨hne, hd⟩
  · have htl : f1.val < a1.val :=
      Store.destruct_fields_lt hinv (.inl rfl) hd f1 (by rw [hv]; simp)
    rw [hd]
    simp only [Std.bind_ok]
    have hvlen : v.length = 2 := by simp [alloc.vec.Vec.length, hv]
    step as ⟨g0, hg0⟩
    have hg0' : f0 = g0 := by simp [hg0, hv]
    subst hg0'
    step as ⟨g1, hg1⟩
    have hg1' : f1 = g1 := by simp [hg1, hv]
    subst hg1'
    step with hb s f0 x0 hinv h64 hrem hf0 as ⟨r1, s2, hinv2, hg2, hr1⟩
    cases r1 with
    | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg2, trivial⟩
    | Ok v3 =>
      simp only
      step with hc s2 f0 x0 hinv2 h64 (hg2.rem hrem) (Represents.grows hf0 hg2)
        as ⟨r2, s3, hinv3, hg3, hr2⟩
      cases r2 with
      | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv3, hg2.trans hg3, trivial⟩
      | Ok v4 =>
        simp only [lift, Std.bind_ok]
        step with Store.builtin_spec_and s3 (Array.to_slice (Array.make 2#usize [v3, v4]))
          (a := v3) (b := v4) (by simp [Std.Array.to_slice, Array.make])
          (Represents.grows hr1 hg3) hr2 hinv3 h64 as ⟨r3, s5, hinv5, hg5, hr3⟩
        cases r3 with
        | Err e =>
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv5, (hg2.trans hg3).trans hg5, trivial⟩
        | Ok v5 =>
          simp only
          step with Store.tick_grows s5 hinv5 as ⟨r4, s6, hinv6, hg6⟩
          have hg := ((hg2.trans hg3).trans hg5).trans hg6
          cases r4 with
          | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv6, hg, trivial⟩
          | Ok u =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv6, hg, x0, xr, rfl, Represents.grows hr3 hg6, ?_, ?_⟩
            · exact Represents.grows hf0 hg
            · exact ⟨Represents.grows hf1 hg, htl⟩
  · rw [hd]
    simp only [Std.bind_ok]
    show (ok (core.result.Result.Ok none, s) :
      Result ((core.result.Result (Option FoldStep) CheckError) × Store)) ⦃ r s' => _ ⦄div
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, hne⟩

/-- One step of the fold: the end of the list, or an assumption with its
guard and the rest. -/
theorem fold_step_spec (m : Nat) (hb : IsBoolTypeSpec m) (hc : IsClosedSpec m) (s : Store)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ m) (a0 a1 : Term)
    {x1 : Eo.CArgList} (h1 : Represents.rep s a1 x1) :
    generated.part0.step_eo__24eo_5finvoke_5fassume_5flist s a0 a1 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (FoldStep.Done t) => x1 = Eo.CArgList.nil ∧ t = a0
      | core.result.Result.Ok (FoldStep.Push g t tl) =>
        ∃ F rest, x1 = Eo.CArgList.cons F rest ∧ Represents.rep s' g (assumeGuard F) ∧
          Represents.rep s' t F ∧ Represents.rep s' tl rest ∧ tl.val < a1.val
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.step_eo__24eo_5finvoke_5fassume_5flist
  step with fold_case0_spec s hinv h64 a0 a1 h1 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok o =>
    cases o with
    | some st =>
      cases st with
      | Done t => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, hr⟩
      | Push g t tl => exact absurd hr id
    | none =>
      simp only
      step with fold_case1_spec m hb hc s1 hinv1 h64 (hg1.rem hrem) a0 a1 (Represents.grows h1 hg1)
        as ⟨r1, s2, hinv2, hg2, hr1⟩
      cases r1 with
      | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg1.trans hg2, trivial⟩
      | Ok o1 =>
        cases o1 with
        | none =>
          exfalso
          cases x1 with
          | nil => exact hr rfl
          | cons F rest => exact hr1 F rest rfl
        | some st =>
          cases st with
          | Done t => exact absurd hr1 id
          | Push g t tl =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv2, hg1.trans hg2, hr1⟩

/-- The scan down the list of assumptions: the state at its end (the fold's
first argument) and each assumption's guard with it, in order. -/
theorem fold_scan_loop_spec (m : Nat) (hb : IsBoolTypeSpec m) (hc : IsClosedSpec m)
    (h64 : Platform64) (a0 : Term) :
    ∀ (args : Term) (s : Store) (pending : alloc.vec.Vec (Term × Term))
      (pairs : List (Eo.Term × Eo.Term)) (xs : Eo.CArgList),
      s.Inv → s.remaining ≤ m → Represents.rep s args xs →
      List.Forall₂ (fun p q => Represents.rep s p.1 q.1 ∧ Represents.rep s p.2 q.2)
        pending.val pairs →
      pending.val.length + args.val < s.nodes.length + 1 →
      generated.part0.scan_eo__24eo_5finvoke_5fassume_5flist_loop args s a0 pending ⦃ r s' =>
        s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok (state, pending') => state = a0 ∧
          List.Forall₂ (fun p q => Represents.rep s' p.1 q.1 ∧ Represents.rep s' p.2 q.2)
            pending'.val (pairs ++ (cargs xs).map (fun F => (assumeGuard F, F)))
        | core.result.Result.Err _ => True ⦄div := by
  apply generated.part0.scan_eo__24eo_5finvoke_5fassume_5flist_loop.fixpoint_induct a0
    (motive := fun loop => ∀ (args : Term) (s : Store) (pending : alloc.vec.Vec (Term × Term))
      (pairs : List (Eo.Term × Eo.Term)) (xs : Eo.CArgList),
      s.Inv → s.remaining ≤ m → Represents.rep s args xs →
      List.Forall₂ (fun p q => Represents.rep s p.1 q.1 ∧ Represents.rep s p.2 q.2)
        pending.val pairs →
      pending.val.length + args.val < s.nodes.length + 1 →
      loop args s pending ⦃ r s' =>
        s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok (state, pending') => state = a0 ∧
          List.Forall₂ (fun p q => Represents.rep s' p.1 q.1 ∧ Represents.rep s' p.2 q.2)
            pending'.val (pairs ++ (cargs xs).map (fun F => (assumeGuard F, F)))
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih args s pending pairs xs hinv hrem hargs hpend hsz
    simp only
    step with fold_step_spec m hb hc s hinv h64 hrem a0 args hargs as ⟨r, s1, hinv1, hg1, hr⟩
    have hpend1 : List.Forall₂ (fun p q => Represents.rep s1 p.1 q.1 ∧ Represents.rep s1 p.2 q.2)
        pending.val pairs :=
      hpend.imp (fun {_ _} h => ⟨Represents.grows h.1 hg1, Represents.grows h.2 hg1⟩)
    cases r with
    | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
    | Ok st =>
      cases st with
      | Done t =>
        obtain ⟨rfl, rfl⟩ := hr
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, trivial, by simpa [cargs] using hpend1⟩
      | Push g t tl =>
        obtain ⟨F, rest, rfl, hg, ht, htl, hlt⟩ := hr
        simp only
        have hmax := hinv1.table.hmax
        have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
        have hcap : pending.val.length < Usize.max := by
          have : s1.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
          have := hg1.nodes.length_le
          simp only [alloc.vec.Vec.length] at hsz this ⊢
          omega
        step with alloc.vec.Vec.push_spec pending (g, t) hcap as ⟨pending1, hp1⟩
        have hpend2 : List.Forall₂ (fun p q => Represents.rep s1 p.1 q.1 ∧ Represents.rep s1 p.2 q.2)
            pending1.val (pairs ++ [(assumeGuard F, F)]) := by
          rw [hp1]; exact List.rel_append hpend1 (List.Forall₂.cons ⟨hg, ht⟩ List.Forall₂.nil)
        have hsz1 : pending1.val.length + tl.val < s1.nodes.length + 1 := by
          have := hg1.nodes.length_le
          rw [hp1]; simp only [List.length_append, List.length_singleton]
          simp only [alloc.vec.Vec.length] at hsz this ⊢
          omega
        apply WP.dspec_mono (ih tl s1 pending1 (pairs ++ [(assumeGuard F, F)]) rest hinv1
          (hg1.rem hrem) htl hpend2 hsz1)
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok p =>
          obtain ⟨state, pending'⟩ := p
          obtain ⟨h1, h2⟩ := hr2
          refine ⟨h1, ?_⟩
          simpa [cargs] using h2

/-- The unwind: from the `i`-th pair down to the first, each pushed with
`$eo_push_input_assume_check` onto the state. -/
theorem fold_unwind_loop_spec (m : Nat) (hp : PushInputSpec m) (h64 : Platform64) (s0 : Store)
    (pending : Slice (Term × Term)) (pairs : List (Eo.Term × Eo.Term))
    (hpend : List.Forall₂ (fun p q => Represents.rep s0 p.1 q.1 ∧ Represents.rep s0 p.2 q.2)
      pending.val pairs)
    (hpairs : ∀ q ∈ pairs, q.1 = Eo.Term.Boolean true → q.2 ≠ Eo.Term.Stuck) :
    ∀ (s : Store) (state : Term) (i : Std.Usize) (xst : Eo.CState),
      s.Inv → s0.Grows s → s.remaining ≤ m → Represents.rep s state xst → i.val ≤ pairs.length →
      StateOK xst →
      generated.part0.unwind_eo__24eo_5finvoke_5fassume_5flist_loop s pending state i ⦃ r s' =>
        s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok t => Represents.rep s' t
            ((pairs.take i.val).foldr (fun q st => Eo.__eo_push_input_assume_check q.1 q.2 st) xst)
        | core.result.Result.Err _ => True ⦄div := by
  have hlen : pending.val.length = pairs.length := hpend.length_eq
  apply generated.part0.unwind_eo__24eo_5finvoke_5fassume_5flist_loop.fixpoint_induct pending
    (motive := fun loop => ∀ (s : Store) (state : Term) (i : Std.Usize) (xst : Eo.CState),
      s.Inv → s0.Grows s → s.remaining ≤ m → Represents.rep s state xst → i.val ≤ pairs.length →
      StateOK xst →
      loop s state i ⦃ r s' =>
        s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok t => Represents.rep s' t
            ((pairs.take i.val).foldr (fun q st => Eo.__eo_push_input_assume_check q.1 q.2 st) xst)
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih s state i xst hinv hg hrem hst hi hok
    simp only
    split
    · rename_i hpos
      step as ⟨i1, hi1⟩
      have hi1lt : i1.val < pending.val.length := by rw [hlen]; scalar_tac
      step as ⟨p, hpv⟩
      obtain ⟨g, t⟩ := p
      have hpe : pending.val[i1.val] = (g, t) := by
        have := hpv.symm
        simpa [Slice.getElem!_Nat_eq, getElem!_eq _ _ hi1lt] using this
      have hq := (List.forall₂_iff_get.mp hpend).2 i1.val hi1lt (by rw [← hlen]; exact hi1lt)
      simp only [List.get_eq_getElem, hpe] at hq
      obtain ⟨hpg, hpt⟩ := hq
      step with hp s g t state _ _ xst hinv h64 hrem (Represents.grows hpg hg) (Represents.grows hpt hg) hst
        hok as ⟨r, s1, hinv1, hg1, hr⟩
      cases r with
      | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
      | Ok v =>
        simp only
        apply WP.dspec_mono (ih s1 v i1 _ hinv1 (hg.trans hg1) (hg1.rem hrem) hr (by scalar_tac)
          (StateOK.push_input_assume_check_of hok (hpairs _ (List.getElem_mem _))))
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok t =>
          simp only at hr2 ⊢
          have hsplit : pairs.take i.val = pairs.take i1.val ++ [pairs[i1.val]'(by rw [← hlen]; exact hi1lt)] := by
            rw [show i.val = i1.val + 1 by scalar_tac, List.take_succ_eq_append_getElem]
          rw [hsplit, List.foldr_append]
          simpa using hr2
    · rename_i hz
      have hi0 : i.val = 0 := by scalar_tac
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, by simpa [hi0] using hst⟩

/-- `$eo_invoke_assume_list`, compiled to the fold: logos's
`__eo_invoke_assume_list`, from what is proved of the three programs it
calls. -/
theorem invoke_assume_list_spec (n : Nat) (hb : ∀ m < n, IsBoolTypeSpec m)
    (hc : ∀ m < n, IsClosedSpec m) (hp : ∀ m < n, PushInputSpec m) :
    ∀ (s : Store) (a0 a1 : Term) (x_a0 : Eo.CState) (x_a1 : Eo.CArgList), s.Inv → Platform64 →
      s.remaining ≤ n → Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
      generated.part0.eo__24eo_5finvoke_5fassume_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_invoke_assume_list x_a0 x_a1)
        | core.result.Result.Err _ => True ⦄div := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
  unfold generated.part0.eo__24eo_5finvoke_5fassume_5flist
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => generated.part0.body_eo__24eo_5finvoke_5fassume_5flist s1 a0 a1)
    (fun s' t => Represents.rep s' t (Eo.__eo_invoke_assume_list x_a0 x_a1))
    (by intro _ _ _ hn h; exact Represents.congr h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      have h0 := Represents.congr h_a0 hn
      have h1 := Represents.congr h_a1 hn
      unfold generated.part0.body_eo__24eo_5finvoke_5fassume_5flist
        generated.part0.scan_eo__24eo_5finvoke_5fassume_5flist
      have hsz : (alloc.vec.Vec.new (Term × Term)).val.length + a1.val < s1.nodes.length + 1 := by
        have := h1.lt; simp only [alloc.vec.Vec.new, alloc.vec.Vec.length] at this ⊢; simp; omega
      step with fold_scan_loop_spec m (hb m hm) (hc m hm) h64 a0 a1 s1 (alloc.vec.Vec.new _) [] x_a1
        hinv1 hrem1 h1 (by simp [alloc.vec.Vec.new]) hsz as ⟨r, s2, hinv2, hg2, hr⟩
      cases r with
      | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg2, trivial⟩
      | Ok v =>
        obtain ⟨state, pending⟩ := v
        obtain ⟨rfl, hpend⟩ := hr
        simp only [List.nil_append] at hpend
        unfold generated.part0.unwind_eo__24eo_5finvoke_5fassume_5flist
        have hpend' : List.Forall₂ (fun p q => Represents.rep s2 p.1 q.1 ∧ Represents.rep s2 p.2 q.2)
            (alloc.vec.Vec.deref pending).val ((cargs x_a1).map (fun F => (assumeGuard F, F))) := by
          simpa [alloc.vec.Vec.deref] using hpend
        have hlenp : (Slice.len (alloc.vec.Vec.deref pending)).val =
            ((cargs x_a1).map (fun F => (assumeGuard F, F))).length := by
          have := hpend'.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (fold_unwind_loop_spec m (hp m hm) h64 s2 (alloc.vec.Vec.deref pending)
          _ hpend' (fun q hq => by
            obtain ⟨F, -, rfl⟩ := List.mem_map.mp hq
            exact fun h => ne_stuck_of_guard h)
          s2 state _ x_a0 hinv2 (Store.Grows.refl s2) (hg2.rem hrem1)
          (Represents.grows h0 hg2) (le_of_eq hlenp) hg_a0)
        rintro ⟨r2, s3⟩ ⟨hinv3, hg3, hr3⟩
        refine ⟨hinv3, hg2.trans hg3, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok t =>
          simp only at hr3 ⊢
          rw [hlenp, List.take_length, List.foldr_map] at hr3
          rw [invoke_assume_list_foldr]
          exact hr3))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
