module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
import all CpcMini.SmtEval
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Store.CacheOps
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Embed

/-!
# The runtime's operations that generated code calls

What each does to the store and what its result stands for, in the form
the generated proofs use: the new store has the invariant, has grown, and
on `Ok` the result is a handle of the stated value.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

theorem empty_args : (Array.to_slice (Std.Array.empty Term)).val = [] := rfl

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
  | Ok t =>
    refine ⟨?_, by simp [Embed.embedded_emb_Term, Embed.emb_Term]⟩
    simp only [Embed.embedded_enc_Term, Embed.enc_Term]
    exact Holds.lit t.val _ hres.1 hres.2


/-- `tick` counts a step of a loop: the terms are as they were, and a
successful tick uses up some of the budget of calls (`Store.budget`). -/
theorem Store.tick_spec (s : Store) :
    Store.tick s ⦃ r s' =>
      s'.nodes = s.nodes ∧ s'.hashes = s.hashes ∧ s'.slots = s.slots ∧
      s'.caches = s.caches ∧ s'.state_jumps = s.state_jumps ∧ s'.limits = s.limits ∧
      s'.depth = s.depth ∧ s'.budget ≤ s.budget ∧
      match r with
      | core.result.Result.Ok _ => s'.budget < s.budget
      | core.result.Result.Err _ => True ⦄ := by
  unfold Store.tick
  split
  · simp
  · step*
    simp only [Store.budget]
    have : s.calls.val < s.limits.calls.val := by scalar_tac
    omega

/-- `native_bool` gives a handle of the native Boolean. -/
theorem Store.native_bool_spec (s : Store) (b : Bool) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_bool s b ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t b
      | core.result.Result.Err _ => True ⦄div := by
  unfold native.Store.native_bool Store.raw
  apply WP.dspec_mono (Store.intern_inv s (TermData.Native (lit.Lit.Boolean b)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact ⟨Holds.native t.val _ hres.1 hres.2, trivial⟩

theorem requires_ne (y t3 r : Eo.Term) (h : y ≠ t3) : Eo.__eo_requires y t3 r = Eo.Term.Stuck := by
  simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h]

theorem requires_stuck (t3 r : Eo.Term) :
    Eo.__eo_requires Eo.Term.Stuck t3 r = Eo.Term.Stuck := by
  simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]

/-- A requirement whose first argument is stuck, without rewriting that
argument elsewhere (the third may depend on proofs that it is not). -/
theorem requires_stuck_of {a b c : Eo.Term} (h : a = Eo.Term.Stuck) :
    Eo.__eo_requires a b c = Eo.Term.Stuck := h ▸ requires_stuck b c

theorem requires_eq (y r : Eo.Term) (h : y ≠ Eo.Term.Stuck) : Eo.__eo_requires y y r = r := by
  simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not, h]

/-- `__eo_requires` as a conditional. -/
theorem requires_ite (a b c : Eo.Term) :
    Eo.__eo_requires a b c =
      if a = b then (if a = Eo.Term.Stuck then Eo.Term.Stuck else c) else Eo.Term.Stuck := by
  by_cases h : a = b
  · by_cases hs : a = Eo.Term.Stuck
    · subst h; subst hs; simp [requires_stuck]
    · subst h; simp [requires_eq _ _ hs, hs]
  · simp [requires_ne _ _ _ h, h]

/-- `__eo_eq` on terms that are not stuck. -/
theorem eo_eq_of_ne (a b : Eo.Term) (ha : a ≠ Eo.Term.Stuck) (hb : b ≠ Eo.Term.Stuck) :
    Eo.__eo_eq a b = Eo.Term.Boolean (decide (b = a)) := by
  unfold Eo.__eo_eq
  split <;> simp_all [Eo.native_teq]

/-- `__eo_eq` says `true` of equal terms that are not stuck, and of no others. -/
theorem eo_eq_true (a b : Eo.Term) :
    Eo.__eo_eq a b = Eo.Term.Boolean true ↔ a = b ∧ a ≠ Eo.Term.Stuck := by
  by_cases ha : a = Eo.Term.Stuck
  · subst ha; simp [Eo.__eo_eq]
  · by_cases hb : b = Eo.Term.Stuck
    · subst hb
      have : Eo.__eo_eq a Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_eq; split <;> simp_all
      simp [this, ha]
    · rw [eo_eq_of_ne a b ha hb]
      simp [ha, eq_comm]

/-! ## Conditionals

The generated `if_k` of `eo::ite c a b` (and of the native `ite`) asks
`boolean_value` for the Boolean the condition's handle stands for, and
computes the branch it names; logos's `__eo_ite` and `native_ite` give the
same, and `__eo_ite` the stuck term on a condition that is no Boolean. -/

/-- `boolean_value` on a handle of a term: its Boolean, if it is one. -/
theorem Store.boolean_value_term {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    (x = Eo.Term.Boolean true ∧
      Store.boolean_value s t false = ok (core.result.Result.Ok (some true))) ∨
    (x = Eo.Term.Boolean false ∧
      Store.boolean_value s t false = ok (core.result.Result.Ok (some false))) ∨
    ((∀ b, x ≠ Eo.Term.Boolean b) ∧
      Store.boolean_value s t false = ok (core.result.Result.Ok none)) := by
  obtain ⟨hh, he⟩ := h
  unfold Store.boolean_value
  rw [Store.view_eq]
  simp only [hh.lt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Bool.false_eq_true, ite_false]
  generalize hx : Embedded.enc x = tx at hh
  cases hh with
  | lit _ l _ hd =>
    rw [hd]
    rcases Embed.inv_Term_lit hx with ⟨b, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · cases b <;> simp
    all_goals (right; right; exact ⟨(fun b h => by cases h), by simp⟩)
  | _ =>
    rename_i hd
    first
      | (rw [hd]; right; right
         refine ⟨fun b h => ?_, by simp⟩
         subst h; simp [Embed.embedded_enc_Term, Embed.enc_Term] at hx)
      | (rename_i _ hd'; rw [hd']; right; right
         refine ⟨fun b h => ?_, by simp⟩
         subst h; simp [Embed.embedded_enc_Term, Embed.enc_Term] at hx)

/-- `boolean_value` on a handle of a native Boolean: that Boolean. -/
theorem Store.boolean_value_native {s : Store} {t : Term} {x : Bool} (h : Represents.rep s t x) :
    (x = true ∧ Store.boolean_value s t true = ok (core.result.Result.Ok (some true))) ∨
    (x = false ∧ Store.boolean_value s t true = ok (core.result.Result.Ok (some false))) := by
  obtain ⟨hh, _⟩ := h
  unfold Store.boolean_value
  rw [Store.view_eq]
  simp only [hh.lt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  simp only [Tree.embedded_enc_Bool, Tree.encBool] at hh
  cases hh with
  | native _ _ _ hd => rw [hd]; cases x <;> simp

theorem eo_ite_true_rep {s : Store} {t : Term} {c a : Eo.Term} (b : Eo.Term)
    (hc : c = Eo.Term.Boolean true) (h : s.Rep t a) : s.Rep t (Eo.__eo_ite c a b) := by
  subst hc; simpa [Eo.__eo_ite, SmtEval.native_ite, Eo.native_teq] using h

theorem eo_ite_false_rep {s : Store} {t : Term} {c b : Eo.Term} (a : Eo.Term)
    (hc : c = Eo.Term.Boolean false) (h : s.Rep t b) : s.Rep t (Eo.__eo_ite c a b) := by
  subst hc; simpa [Eo.__eo_ite, SmtEval.native_ite, Eo.native_teq] using h

theorem eo_ite_stuck_rep {s : Store} {t : Term} {c : Eo.Term} (a b : Eo.Term)
    (hc : ∀ x, c ≠ Eo.Term.Boolean x) (h : s.Rep t Eo.Term.Stuck) :
    s.Rep t (Eo.__eo_ite c a b) := by
  have h1 : (c = Eo.Term.Boolean true) = False := by simpa using hc true
  have h2 : (c = Eo.Term.Boolean false) = False := by simpa using hc false
  simpa [Eo.__eo_ite, SmtEval.native_ite, Eo.native_teq, h1, h2] using h

theorem native_ite_true_rep {α : Type} [Embedded α] {s : Store} {t : Term} {c : Bool} {a : α}
    (b : α) (hc : c = true) (h : Represents.rep s t a) :
    Represents.rep s t (SmtEval.native_ite c a b) := by
  subst hc; simpa [SmtEval.native_ite] using h

theorem native_ite_false_rep {α : Type} [Embedded α] {s : Store} {t : Term} {c : Bool} {b : α}
    (a : α) (hc : c = false) (h : Represents.rep s t b) :
    Represents.rep s t (SmtEval.native_ite c a b) := by
  subst hc; simpa [SmtEval.native_ite] using h

/-- `apply` builds logos's guarded application `__eo_mk_apply`: the stuck
term when either part is stuck, the application otherwise. lean-meta writes
`__eo_mk_apply` where the application has a part that is evaluated
(`lean_meta_reduce.cpp`), and the generated code's `apply` is this; no
hypothesis that the parts are not stuck is needed. -/
theorem Store.apply_mk_rep (s : Store) (f a : Term) (x y : Eo.Term) (hinv : s.Inv)
    (h64 : Platform64) (hf : s.Rep f x) (ha : s.Rep a y) :
    Store.apply s f a ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_mk_apply x y)
      | core.result.Result.Err _ => True ⦄div := by
  by_cases hx : x = Eo.Term.Stuck
  · subst hx
    apply WP.dspec_mono (Store.apply_spec s f a hinv h64)
    rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
    simp only [WP.uncurry'_pair] at hres ⊢
    refine ⟨hinv', hext.grows, ?_⟩
    cases r with
    | Err e => trivial
    | Ok t =>
      simp only at hres ⊢
      obtain ⟨_, _, hres⟩ := hres
      have hs : (s.data f).isStuck = true := hf.stuck_iff.mpr rfl
      simp only [hs, ite_true] at hres
      obtain ⟨rfl, rfl⟩ := hres
      simpa [Eo.__eo_mk_apply] using hinv.rep_stuck
  by_cases hy : y = Eo.Term.Stuck
  · subst hy
    apply WP.dspec_mono (Store.apply_spec s f a hinv h64)
    rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
    simp only [WP.uncurry'_pair] at hres ⊢
    refine ⟨hinv', hext.grows, ?_⟩
    cases r with
    | Err e => trivial
    | Ok t =>
      simp only at hres ⊢
      obtain ⟨_, _, hres⟩ := hres
      have hfs : (s.data f).isStuck = false := by
        cases h : (s.data f).isStuck
        · rfl
        · exact absurd (hf.stuck_iff.mp h) hx
      have has : (s.data a).isStuck = true := ha.stuck_iff.mpr rfl
      simp only [hfs, has, Bool.false_eq_true, ite_false, ite_true] at hres
      obtain ⟨_, rfl, rfl⟩ := hres
      have : Eo.__eo_mk_apply x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_mk_apply; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
  have : Eo.__eo_mk_apply x y = Eo.Term.Apply x y := by
    unfold Eo.__eo_mk_apply; split <;> simp_all
  rw [this]
  exact Store.apply_rep s f a x y hinv h64 hf ha hx hy

/-- A program whose results are cached: `enter`, a look in the cache, else
the body, `leave`, and the result put in the cache. What holds of the body
holds of the program, if what the cache says of the program (`hget`,
`hput`) is what is to be proved of it. -/
theorem Store.framed_cached (s : Store) (hinv : s.Inv) {n : Nat} (hrem : s.remaining ≤ n)
    (pid : cache.ProgramId) (sl : Slice Term) (args : List Term) (hsl : sl.val = args)
    (body : Store → Result ((core.result.Result Term CheckError) × Store))
    (post : Store → Term → Prop)
    (hpost : ∀ (s1 s2 : Store) (a : Term), s2.nodes = s1.nodes → post s1 a → post s2 a)
    (hget : ∀ (s1 : Store) (res : Term), s1.nodes = s.nodes →
      ProgramSem s1.nodes.val pid.val args res → post s1 res)
    (hput : ∀ (s1 : Store) (res : Term), s.nodes.val <+: s1.nodes.val → post s1 res →
      ProgramSem s1.nodes.val pid.val args res)
    (hbody : ∀ (s1 : Store) (m : Nat), s1.Inv → s1.nodes = s.nodes → m < n →
      s1.remaining ≤ m →
      body s1 ⦃ r s2 => s2.Inv ∧ s1.Grows s2 ∧
        match r with
        | core.result.Result.Ok a => post s2 a
        | core.result.Result.Err _ => True ⦄div) :
    (do
      let (r, s1) ← Store.enter s
      match r with
      | core.result.Result.Ok _ =>
        let s2 ← lift sl
        let (r1, s3) ← Store.cached_program s1 pid s2
        match r1 with
        | core.result.Result.Ok o =>
          match o with
          | none =>
            let (result, s4) ← body s3
            let s5 ← Store.leave s4
            match result with
            | core.result.Result.Ok value =>
              let s6 ← lift sl
              let (r2, s7) ← Store.cache_program s5 pid s6 value
              match r2 with
              | core.result.Result.Ok _ => ok (result, s7)
              | core.result.Result.Err e => ok (core.result.Result.Err e, s7)
            | core.result.Result.Err _ => ok (result, s5)
          | some value =>
            let s4 ← Store.leave s3
            ok (core.result.Result.Ok value, s4)
        | core.result.Result.Err error =>
          let s4 ← Store.leave s3
          ok (core.result.Result.Err error, s4)
      | core.result.Result.Err e => ok (core.result.Result.Err e, s1)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok a => post s' a
      | core.result.Result.Err _ => True ⦄div := by
  step with Store.enter_spec as ⟨r, s1, hn, hh, hs, hc, hj, hl, hb, hd⟩
  have hinv1 : s1.Inv := hinv.congr hn hh hs hc hj
  cases r with
  | Err e =>
    simp only [WP.dspec_ok, WP.uncurry'_pair] at hd ⊢
    exact ⟨hinv1, ⟨by rw [hn], hl, hd, hb⟩, trivial⟩
  | Ok u =>
    simp only at hd ⊢
    obtain ⟨hd, hlim⟩ := hd
    have hrem1 : s1.remaining ≤ n - 1 := by
      unfold Store.remaining at hrem ⊢; rw [hl, hd]; omega
    have hn0 : n - 1 < n := by unfold Store.remaining at hrem; omega
    simp only [lift, Std.bind_ok]
    step with Store.cached_program_spec s1 hinv1 pid sl as ⟨r1, s3, hinv3, hg3, hn3, hr1⟩
    have hd3 : 0 < s3.depth.val := by rw [hg3.depth, hd]; omega
    have hd3v : s3.depth.val = s.depth.val + 1 := by rw [hg3.depth, hd]
    have hl3 : s3.limits = s.limits := by rw [hg3.limits, hl]
    have hn3' : s3.nodes = s.nodes := by rw [hn3, hn]
    have hrem3 : s3.remaining ≤ n - 1 := hg3.rem hrem1
    cases r1 with
    | Err error =>
      clear hr1
      dsimp only
      step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hj4, hl4, hd4, hk4⟩
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv3.congr hn4 hh4 hs4 hc4 hj4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_,
          by rw [Store.budget_congr hl4 hk4]; exact le_trans hg3.budget hb⟩, trivial⟩
      exact u32_eq_of_val (by rw [hd4, hd3v]; omega)
    | Ok o =>
      cases o with
      | some value =>
        have hr1' : ∃ e, e ∈ s1.caches.programs.entries.val ∧ e.program = pid ∧
            e.args.val = sl.val ∧ e.result = value := hr1
        clear hr1
        dsimp only
        obtain ⟨e, he, hep, hea, her⟩ := hr1'
        have hsem : ProgramSem s3.nodes.val pid.val args value := by
          have := hinv1.cache.entries e he
          unfold EntryOK at this
          rw [hep, hea, hsl, her] at this
          rw [hn3]; exact this
        have hval : post s3 value := hget s3 value hn3' hsem
        step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hj4, hl4, hd4, hk4⟩
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv3.congr hn4 hh4 hs4 hc4 hj4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_,
          by rw [Store.budget_congr hl4 hk4]; exact le_trans hg3.budget hb⟩,
          hpost s3 s4 value hn4 hval⟩
        exact u32_eq_of_val (by rw [hd4, hd3v]; omega)
      | none =>
        clear hr1
        simp only
        step with hbody s3 (n - 1) hinv3 hn3' hn0 hrem3 as ⟨result, s4, hinv4, hg4, hres⟩
        have hd4 : 0 < s4.depth.val := by rw [hg4.depth]; exact hd3
        step with Store.leave_spec s4 hd4 as ⟨s5, hn5, hh5, hs5, hc5, hj5, hl5, hd5, hk5⟩
        have hb5 : s5.budget ≤ s.budget := by
          rw [Store.budget_congr hl5 hk5]; exact le_trans hg4.budget (le_trans hg3.budget hb)
        have hinv5 : s5.Inv := hinv4.congr hn5 hh5 hs5 hc5 hj5
        have hnodes5 : s.nodes.val <+: s5.nodes.val := by
          rw [hn5, ← hn3']; exact hg4.nodes
        have hl5' : s5.limits = s.limits := by rw [hl5, hg4.limits, hl3]
        have hd5' : s5.depth = s.depth := by
          exact u32_eq_of_val (by rw [hd5, hg4.depth, hd3v]; omega)
        cases result with
        | Err e =>
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv5, ⟨hnodes5, hl5', hd5', hb5⟩, trivial⟩
        | Ok value =>
          simp only at hres ⊢
          have hval5 : post s5 value := hpost s4 s5 value hn5 hres
          step with Store.cache_program_spec s5 hinv5 pid sl value
            (by
              intro key hkey
              unfold EntryOK
              simp only
              rw [hkey, hsl]
              exact hput s5 value hnodes5 hval5)
            as ⟨r2, s7, hinv7, hg7, hn7⟩
          cases r2 with
          | Err e =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv7, ⟨hnodes5.trans hg7.nodes, by rw [hg7.limits, hl5'],
              by rw [hg7.depth, hd5'], le_trans hg7.budget hb5⟩, trivial⟩
          | Ok u2 =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv7, ⟨hnodes5.trans hg7.nodes, by rw [hg7.limits, hl5'],
              by rw [hg7.depth, hd5'], le_trans hg7.budget hb5⟩, hpost s5 s7 value hn7 hval5⟩

/-- A program whose results are kept in the type cache (`$eo_typeof`,
`$smtx_typeof`): as `framed_cached`, with the row of its one argument in
place of an entry of the cache of program results. -/
theorem Store.framed_type_cached (s : Store) (hinv : s.Inv) {n : Nat} (hrem : s.remaining ≤ n)
    (h64 : Platform64) (k : cache.TypeCacheKind) (a0 : Term)
    (body : Store → Result ((core.result.Result Term CheckError) × Store))
    (post : Store → Term → Prop)
    (hpost : ∀ (s1 s2 : Store) (a : Term), s2.nodes = s1.nodes → post s1 a → post s2 a)
    (hget : ∀ (s1 : Store) (res : Term), s1.nodes = s.nodes →
      ProgramSem s1.nodes.val (typeSemId k) [a0] res → post s1 res)
    (hput : ∀ (s1 : Store) (res : Term), s.nodes.val <+: s1.nodes.val → post s1 res →
      ProgramSem s1.nodes.val (typeSemId k) [a0] res)
    (hbody : ∀ (s1 : Store) (m : Nat), s1.Inv → s1.nodes = s.nodes → m < n →
      s1.remaining ≤ m →
      body s1 ⦃ r s2 => s2.Inv ∧ s1.Grows s2 ∧
        match r with
        | core.result.Result.Ok a => post s2 a
        | core.result.Result.Err _ => True ⦄div) :
    (do
      let (r, s1) ← Store.enter s
      match r with
      | core.result.Result.Ok _ =>
        let t ← Array.index_usize (Array.make 1#usize [ a0 ]) 0#usize
        let (r1, s2) ← Store.cached_type s1 k t
        match r1 with
        | core.result.Result.Ok o =>
          match o with
          | none =>
            let (result, s3) ← body s2
            let s4 ← Store.leave s3
            match result with
            | core.result.Result.Ok value =>
              let (r2, s5) ← Store.cache_type s4 k t value
              match r2 with
              | core.result.Result.Ok _ => ok (result, s5)
              | core.result.Result.Err e => ok (core.result.Result.Err e, s5)
            | core.result.Result.Err _ => ok (result, s4)
          | some value =>
            let s3 ← Store.leave s2
            ok (core.result.Result.Ok value, s3)
        | core.result.Result.Err error =>
          let s3 ← Store.leave s2
          ok (core.result.Result.Err error, s3)
      | core.result.Result.Err e => ok (core.result.Result.Err e, s1)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok a => post s' a
      | core.result.Result.Err _ => True ⦄div := by
  step with Store.enter_spec as ⟨r, s1, hn, hh, hs, hc, hj, hl, hb, hd⟩
  have hinv1 : s1.Inv := hinv.congr hn hh hs hc hj
  cases r with
  | Err e =>
    simp only [WP.dspec_ok, WP.uncurry'_pair] at hd ⊢
    exact ⟨hinv1, ⟨by rw [hn], hl, hd, hb⟩, trivial⟩
  | Ok u =>
    simp only at hd ⊢
    obtain ⟨hd, hlim⟩ := hd
    have hrem1 : s1.remaining ≤ n - 1 := by
      unfold Store.remaining at hrem ⊢; rw [hl, hd]; omega
    have hn0 : n - 1 < n := by unfold Store.remaining at hrem; omega
    have hidx : Array.index_usize (Array.make 1#usize [ a0 ]) 0#usize = ok a0 := by
      simp [Array.index_usize, Array.make]
    simp only [hidx, Std.bind_ok]
    step with Store.cached_type_spec s1 hinv1 k a0 as ⟨r1, s3, hinv3, hg3, hn3, hr1⟩
    have hd3 : 0 < s3.depth.val := by rw [hg3.depth, hd]; omega
    have hd3v : s3.depth.val = s.depth.val + 1 := by rw [hg3.depth, hd]
    have hl3 : s3.limits = s.limits := by rw [hg3.limits, hl]
    have hn3' : s3.nodes = s.nodes := by rw [hn3, hn]
    have hrem3 : s3.remaining ≤ n - 1 := hg3.rem hrem1
    cases r1 with
    | Err error =>
      clear hr1
      dsimp only
      step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hj4, hl4, hd4, hk4⟩
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv3.congr hn4 hh4 hs4 hc4 hj4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_,
          by rw [Store.budget_congr hl4 hk4]; exact le_trans hg3.budget hb⟩, trivial⟩
      exact u32_eq_of_val (by rw [hd4, hd3v]; omega)
    | Ok o =>
      cases o with
      | some value =>
        have hsem : ProgramSem s3.nodes.val (typeSemId k) [a0] value := by
          rw [hn3]; exact hr1
        clear hr1
        dsimp only
        have hval : post s3 value := hget s3 value hn3' hsem
        step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hj4, hl4, hd4, hk4⟩
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv3.congr hn4 hh4 hs4 hc4 hj4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_,
          by rw [Store.budget_congr hl4 hk4]; exact le_trans hg3.budget hb⟩,
          hpost s3 s4 value hn4 hval⟩
        exact u32_eq_of_val (by rw [hd4, hd3v]; omega)
      | none =>
        clear hr1
        simp only
        step with hbody s3 (n - 1) hinv3 hn3' hn0 hrem3 as ⟨result, s4, hinv4, hg4, hres⟩
        have hd4 : 0 < s4.depth.val := by rw [hg4.depth]; exact hd3
        step with Store.leave_spec s4 hd4 as ⟨s5, hn5, hh5, hs5, hc5, hj5, hl5, hd5, hk5⟩
        have hb5 : s5.budget ≤ s.budget := by
          rw [Store.budget_congr hl5 hk5]; exact le_trans hg4.budget (le_trans hg3.budget hb)
        have hinv5 : s5.Inv := hinv4.congr hn5 hh5 hs5 hc5 hj5
        have hnodes5 : s.nodes.val <+: s5.nodes.val := by
          rw [hn5, ← hn3']; exact hg4.nodes
        have hl5' : s5.limits = s.limits := by rw [hl5, hg4.limits, hl3]
        have hd5' : s5.depth = s.depth := by
          exact u32_eq_of_val (by rw [hd5, hg4.depth, hd3v]; omega)
        cases result with
        | Err e =>
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv5, ⟨hnodes5, hl5', hd5', hb5⟩, trivial⟩
        | Ok value =>
          simp only at hres ⊢
          have hval5 : post s5 value := hpost s4 s5 value hn5 hres
          step with Store.cache_type_spec s5 hinv5 h64 k a0 value (hput s5 value hnodes5 hval5)
            as ⟨r2, s7, hinv7, hg7, hn7⟩
          cases r2 with
          | Err e =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv7, ⟨hnodes5.trans hg7.nodes, by rw [hg7.limits, hl5'],
              by rw [hg7.depth, hd5'], le_trans hg7.budget hb5⟩, trivial⟩
          | Ok u2 =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv7, ⟨hnodes5.trans hg7.nodes, by rw [hg7.limits, hl5'],
              by rw [hg7.depth, hd5'], le_trans hg7.budget hb5⟩, hpost s5 s7 value hn7 hval5⟩

end pathos_compiled_checker
