module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem

/-!
# Looking a program's result up, and keeping it

`Store.cached_program` and `Store.cache_program`, which a cached program
calls before and after its body.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The invariant is about the terms, their table, the rows of the type
cache and the cache of program results. -/
theorem Store.Inv.congr' {s s' : Store} (h : s.Inv) (hn : s'.nodes = s.nodes)
    (hh : s'.hashes = s.hashes) (hs : s'.slots = s.slots)
    (hct : s'.caches.types = s.caches.types)
    (hcp : s'.caches.programs = s.caches.programs) : s'.Inv := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [hn, hh, hs, hct, hcp] <;> assumption

/-- The same when the cache of program results changes, if it stays right. -/
theorem Store.Inv.with_cache {s s' : Store} (h : s.Inv) (hn : s'.nodes = s.nodes)
    (hh : s'.hashes = s.hashes) (hs : s'.slots = s.slots)
    (hct : s'.caches.types = s.caches.types) (hc : CacheInv s') : s'.Inv := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, _⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hc⟩ <;>
    simp only [hn, hh, hs, hct] <;> assumption

theorem cache.Caches.program_get_spec (c : cache.Caches) (hwf : CacheWf c.programs)
    (program : cache.ProgramId) (args : Slice Term) :
    cache.Caches.program_get c program args ⦃ r c' =>
      c'.types = c.types ∧ c'.programs = c.programs ∧
      ∀ v, r = some v → ∃ e, e ∈ c.programs.entries.val ∧ e.program = program ∧
        e.args.val = args.val ∧ e.result = v ⦄div := by
  unfold cache.Caches.program_get
  split
  · step with cache.ProgramCache.get_spec c.programs hwf as ⟨result, hres⟩
    by_cases hs : result.isSome = true
    · simp [hs, lift]; exact hres
    · simp [hs, lift]; exact hres
  · simp

theorem cache.Caches.program_insert_spec (c : cache.Caches) (hwf : CacheWf c.programs)
    (program : cache.ProgramId) (args : Slice Term) (result : Term) :
    cache.Caches.program_insert c program args result ⦃ c' =>
      c'.types = c.types ∧ CacheAdds c.programs c'.programs program args result ⦄div := by
  unfold cache.Caches.program_insert
  split
  · step with cache.ProgramCache.insert_spec c.programs hwf as ⟨pc, hpc⟩
    simp only [WP.dspec_ok]
    exact ⟨trivial, hpc⟩
  · simp only [WP.dspec_ok]
    exact ⟨trivial, hwf, rfl, Or.inl rfl⟩

/-- `cached_program`: the terms are untouched, and a result it answers is
that of an entry of the cache with that program and those arguments. -/
theorem Store.cached_program_spec (s : Store) (hinv : s.Inv) (program : cache.ProgramId)
    (args : Slice Term) :
    Store.cached_program s program args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧ s'.nodes = s.nodes ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ e, e ∈ s.caches.programs.entries.val ∧ e.program = program ∧
          e.args.val = args.val ∧ e.result = v
      | _ => True ⦄div := by
  unfold Store.cached_program
  generalize 0#usize = i
  revert i
  apply Store.cached_program_loop.fixpoint_induct s program args
    (motive := fun f => ∀ i : Std.Usize, f i ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧ s'.nodes = s.nodes ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ e, e ∈ s.caches.programs.entries.val ∧ e.program = program ∧
          e.args.val = args.val ∧ e.result = v
      | _ => True ⦄div)
  · prove_adm
  · intro loop ih i
    simp only
    split
    · step as ⟨t, ht⟩
      rw [Store.view_eq]
      by_cases hv : t.val < s.nodes.length
      · simp only [hv, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        step as ⟨i2, hi2⟩
        exact ih i2
      · simp [hv, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact ⟨hinv, Store.Grows.refl s⟩
    · step with cache.Caches.program_get_spec s.caches hinv.cache.wf as ⟨o, c, hct, hcp, hres⟩
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv.congr' rfl rfl rfl hct hcp, ⟨List.prefix_refl _, rfl, rfl⟩, trivial, ?_⟩
      cases o with
      | none => trivial
      | some v => exact hres v rfl

/-- `cache_program` with a result that is the program's on those arguments:
the terms are untouched and the invariant holds. -/
theorem Store.cache_program_spec (s : Store) (hinv : s.Inv) (program : cache.ProgramId)
    (args : Slice Term) (result : Term)
    (hnew : ∀ key : alloc.vec.Vec Term, key.val = args.val →
      EntryOK s.nodes.val { program, args := key, result }) :
    Store.cache_program s program args result ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧ s'.nodes = s.nodes ⦄div := by
  unfold Store.cache_program
  generalize 0#usize = i
  revert i
  apply Store.cache_program_loop.fixpoint_induct s program args result
    (motive := fun f => ∀ i : Std.Usize, f i ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧ s'.nodes = s.nodes ⦄div)
  · prove_adm
  · intro loop ih i
    simp only
    split
    · step as ⟨t, ht⟩
      rw [Store.view_eq]
      by_cases hv : t.val < s.nodes.length
      · simp only [hv, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        step as ⟨i2, hi2⟩
        exact ih i2
      · simp [hv, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact ⟨hinv, Store.Grows.refl s⟩
    · rw [Store.view_eq]
      by_cases hv : result.val < s.nodes.length
      · simp only [hv, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        step with cache.Caches.program_insert_spec s.caches hinv.cache.wf as ⟨c, hct, hadds⟩
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv.with_cache rfl rfl rfl hct ?_, ⟨List.prefix_refl _, rfl, rfl⟩, trivial⟩
        obtain ⟨hwf', _, hent⟩ := hadds
        refine ⟨hwf', ?_⟩
        intro e he
        rcases hent with hsame | ⟨key, hkey, happ⟩
        · have he' : e ∈ s.caches.programs.entries.val := by
            have : c.programs.entries.val = s.caches.programs.entries.val := by rw [hsame]
            rw [← this]; exact he
          exact hinv.cache.entries e he'
        · have he' : e ∈ s.caches.programs.entries.val ++
              [({ program, args := key, result } : cache.ProgramEntry)] := by
            rw [← happ]; exact he
          rcases List.mem_append.mp he' with h1 | h2
          · exact hinv.cache.entries e h1
          · have : e = { program, args := key, result } := by simpa using h2
            rw [this]; exact hnew key hkey
      · simp [hv, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact ⟨hinv, Store.Grows.refl s⟩

end pathos_compiled_checker
