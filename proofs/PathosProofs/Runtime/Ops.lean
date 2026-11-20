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
  step with Store.enter_spec as ⟨r, s1, hn, hh, hs, hc, hl, hd⟩
  have hinv1 : s1.Inv := hinv.congr hn hh hs hc
  cases r with
  | Err e =>
    simp only [WP.dspec_ok, WP.uncurry'_pair] at hd ⊢
    exact ⟨hinv1, ⟨by rw [hn], hl, hd⟩, trivial⟩
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
      step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hl4, hd4⟩
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv3.congr hn4 hh4 hs4 hc4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_⟩, trivial⟩
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
        step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hl4, hd4⟩
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv3.congr hn4 hh4 hs4 hc4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_⟩,
          hpost s3 s4 value hn4 hval⟩
        exact u32_eq_of_val (by rw [hd4, hd3v]; omega)
      | none =>
        clear hr1
        simp only
        step with hbody s3 (n - 1) hinv3 hn3' hn0 hrem3 as ⟨result, s4, hinv4, hg4, hres⟩
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
              by rw [hg7.depth, hd5']⟩, trivial⟩
          | Ok u2 =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv7, ⟨hnodes5.trans hg7.nodes, by rw [hg7.limits, hl5'],
              by rw [hg7.depth, hd5']⟩, hpost s5 s7 value hn7 hval5⟩

end pathos_compiled_checker
