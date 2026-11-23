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
    (hcp : s'.caches.programs = s.caches.programs)
    (hcs : s'.caches.stats.type_entries = s.caches.stats.type_entries)
    (hj : s'.state_jumps = s.state_jumps) : s'.Inv := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4⟩, d⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [hn, hh, hs, hct, hcp, hcs, hj] <;> assumption

/-- The same when the cache of program results changes, if it stays right. -/
theorem Store.Inv.with_cache {s s' : Store} (h : s.Inv) (hn : s'.nodes = s.nodes)
    (hh : s'.hashes = s.hashes) (hs : s'.slots = s.slots)
    (hct : s'.caches.types = s.caches.types) (hc : CacheInv s')
    (hj : s'.state_jumps = s.state_jumps) : s'.Inv := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, _, d⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hc, ?_⟩ <;>
    simp only [hn, hh, hs, hct, hj] <;> assumption

theorem cache.Caches.program_get_spec (c : cache.Caches) (hwf : CacheWf c.programs)
    (program : cache.ProgramId) (args : Slice Term) :
    cache.Caches.program_get c program args ⦃ r c' =>
      c'.types = c.types ∧ c'.programs = c.programs ∧
      c'.stats.type_entries = c.stats.type_entries ∧
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
      c'.types = c.types ∧ c'.stats = c.stats ∧
        CacheAdds c.programs c'.programs program args result ⦄div := by
  unfold cache.Caches.program_insert
  split
  · step with cache.ProgramCache.insert_spec c.programs hwf as ⟨pc, hpc⟩
    simp only [WP.dspec_ok]
    exact ⟨trivial, trivial, hpc⟩
  · simp only [WP.dspec_ok]
    exact ⟨trivial, trivial, hwf, rfl, Or.inl rfl⟩

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
    · step with cache.Caches.program_get_spec s.caches hinv.cache.wf as ⟨o, c, hct, hcp, hcs, hres⟩
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv.congr' rfl rfl rfl hct hcp hcs rfl, ⟨List.prefix_refl _, rfl, rfl, le_refl _⟩, trivial, ?_⟩
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
        step with cache.Caches.program_insert_spec s.caches hinv.cache.wf as ⟨c, hct, hcs, hadds⟩
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv.with_cache rfl rfl rfl hct ?_ rfl, ⟨List.prefix_refl _, rfl, rfl, le_refl _⟩, trivial⟩
        obtain ⟨hwf', _, hent⟩ := hadds
        refine ⟨hwf', ?_, by rw [hct]; exact hinv.cache.types,
          by rw [hct, hcs]; exact hinv.cache.count⟩
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

/-! ## The type cache -/

theorem cache.Caches.type_get_spec (c : cache.Caches) (k : cache.TypeCacheKind) (t : Term) :
    cache.Caches.type_get c k t ⦃ r c' =>
      c'.types = c.types ∧ c'.programs = c.programs ∧
      c'.stats.type_entries = c.stats.type_entries ∧
      ∀ v, r = some v → ∃ e, c.types.val[(t.val : Nat)]? = some e ∧ e.slot k = some v ⦄ := by
  unfold cache.Caches.type_get
  split
  · step as ⟨i, hi⟩
    split
    · simp
    · rename_i hlt
      step as ⟨e, he⟩
      have hiv : (i : Nat) = (t : Nat) := by subst hi; simp
      have hlt' : (i : Nat) < c.types.val.length := by
        have : ¬ (c.types.len ≤ i) := hlt
        simp [alloc.vec.Vec.len] at this; scalar_tac
      have hget : c.types.val[(t : Nat)]? = some e := by
        rw [← hiv, he, List.getElem?_eq_getElem hlt']
      cases k <;> simp only [Std.bind_ok] <;> split_ifs with hs <;>
        simp [lift, cache.TypeEntry.slot, hget, hs]
  · simp

theorem list_set_opt_none {α : Type} (l : List α) (i : Nat) : List.set_opt l i none = l := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih => cases i <;> simp [ih]

theorem list_set_opt_some {α : Type} (l : List α) (i : Nat) (x : α) :
    List.set_opt l i (some x) = l.set i x := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih => cases i <;> simp [ih]

/-- The number of filled slots of a row. -/
def cache.TypeEntry.filled (e : cache.TypeEntry) : Nat :=
  (if e.eo.isSome then 1 else 0) + (if e.smt.isSome then 1 else 0)

theorem typesFilled_set (l : List cache.TypeEntry) (j : Nat) (e e' : cache.TypeEntry)
    (he : l[j]? = some e) :
    typesFilled (l.set j e') + e.filled = typesFilled l + e'.filled := by
  induction l generalizing j with
  | nil => simp at he
  | cons hd tl ih =>
    cases j with
    | zero =>
      simp at he; subst he
      simp [typesFilled, cache.TypeEntry.filled]; omega
    | succ j =>
      simp at he
      have := ih j he
      simp only [typesFilled, List.set_cons_succ, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- Writing a slot of a row with a result that the table says is right
keeps the type cache right. -/
theorem TypesOK.set {nodes : List TermData} {l : List cache.TypeEntry} (h : TypesOK nodes l)
    (t : Term) (e e' : cache.TypeEntry) (he : l[(t.val : Nat)]? = some e)
    (k : cache.TypeCacheKind) (r : Term) (hr : ProgramSem nodes (typeSemId k) [t] r)
    (hslot : ∀ kk rr, e'.slot kk = some rr → (kk = k ∧ rr = r) ∨ e.slot kk = some rr) :
    TypesOK nodes (l.set (t.val : Nat) e') := by
  intro u f hf kk rr hrr
  by_cases hu : (u.val : Nat) = (t.val : Nat)
  · have hut : u = t := UScalar.eq_of_val_eq hu
    subst hut
    have hlt : (u.val : Nat) < l.length := (List.getElem?_eq_some_iff.mp he).1
    rw [List.getElem?_set_self hlt] at hf
    cases hf
    rcases hslot kk rr hrr with ⟨rfl, rfl⟩ | hold
    · exact hr
    · exact h u e he kk rr hold
  · rw [List.getElem?_set_ne (Ne.symm hu)] at hf
    exact h u f hf kk rr hrr

theorem cache.Caches.type_insert_spec (c : cache.Caches) (k : cache.TypeCacheKind) (t r : Term)
    (nodes : List TermData) (hok : TypesOK nodes c.types.val)
    (hcount : c.stats.type_entries.val ≤ typesFilled c.types.val)
    (hbound : 2 * c.types.length < Usize.max)
    (hr : ProgramSem nodes (typeSemId k) [t] r) :
    cache.Caches.type_insert c k t r ⦃ c' =>
      c'.programs = c.programs ∧ c'.types.length = c.types.length ∧
      TypesOK nodes c'.types.val ∧ c'.stats.type_entries.val ≤ typesFilled c'.types.val ⦄ := by
  unfold cache.Caches.type_insert
  split
  · simp only [lift, Std.bind_ok, alloc.vec.Vec.deref_mut, core.slice.Slice.get_mut,
      core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get_mut]
    have hi : ((UScalar.cast UScalarTy.Usize t : Std.Usize) : Nat) = (t.val : Nat) := by simp
    generalize hio : (UScalar.cast UScalarTy.Usize t : Std.Usize) = i at hi ⊢
    have hval : c.types.slice.val = c.types.val := rfl
    have hsv : ∀ x : Option cache.TypeEntry,
        (c.types.slice.set_opt i x).val = List.set_opt c.types.val (t.val : Nat) x := by
      intro x; rw [Slice.set_opt_val_eq, hi]; rfl
    cases ho : c.types.slice[i]? with
    | none =>
      have ho' : (c.types.slice.val)[(i : Nat)]? = none := by simpa using ho
      simp [ho']
      have hs : ({ slice := c.types.slice.set_opt i none } : alloc.vec.Vec cache.TypeEntry).val =
          c.types.val := by
        show (c.types.slice.set_opt i none).val = _
        rw [hsv, list_set_opt_none]
      simp only [hs]
      exact ⟨trivial, hok, hcount⟩
    | some e =>
      have ho' : (c.types.slice.val)[(i : Nat)]? = some e := by simpa using ho
      have he : c.types.val[(t.val : Nat)]? = some e := by rw [← hi]; exact ho'
      have hlt : (t.val : Nat) < c.types.val.length := (List.getElem?_eq_some_iff.mp he).1
      have hfill := typesFilled_le c.types.val
      have hset : ∀ e' : cache.TypeEntry,
          ({ slice := c.types.slice.set_opt i (some e') } : alloc.vec.Vec cache.TypeEntry).val =
            c.types.val.set (t.val : Nat) e' := by
        intro e'
        show (c.types.slice.set_opt i (some e')).val = _
        rw [hsv, list_set_opt_some]
      have hlen : ∀ e' : cache.TypeEntry, (c.types.val.set (t.val : Nat) e').length =
          c.types.val.length := fun e' => List.length_set
      simp [ho']
      cases k
      · simp only [Std.bind_ok]
        by_cases hs : e.eo = none
        · simp [hs]
          have hlt' : c.stats.type_entries.val + 1 ≤ Usize.max := by
            simp [alloc.vec.Vec.length] at hbound; omega
          step as ⟨i1, hi1⟩
          simp only [hset, hlen, true_and]
          have hf := typesFilled_set c.types.val (t.val : Nat) e { eo := some r, smt := e.smt } he
          refine ⟨hok.set t e _ he _ r hr ?_, ?_⟩
          · intro kk rr h; cases kk <;> simp [cache.TypeEntry.slot] at h ⊢ <;> simp_all
          · simp [cache.TypeEntry.filled, hs] at hf; omega
        · simp [hs]
          simp only [hset, hlen, true_and]
          have hf := typesFilled_set c.types.val (t.val : Nat) e { eo := some r, smt := e.smt } he
          refine ⟨hok.set t e _ he _ r hr ?_, ?_⟩
          · intro kk rr h; cases kk <;> simp [cache.TypeEntry.slot] at h ⊢ <;> simp_all
          · have : e.eo.isSome = true := by cases h : e.eo <;> simp_all
            simp [cache.TypeEntry.filled, this] at hf; omega
      · simp only [Std.bind_ok]
        by_cases hs : e.smt = none
        · simp [hs]
          have hlt' : c.stats.type_entries.val + 1 ≤ Usize.max := by
            simp [alloc.vec.Vec.length] at hbound; omega
          step as ⟨i1, hi1⟩
          simp only [hset, hlen, true_and]
          have hf := typesFilled_set c.types.val (t.val : Nat) e { eo := e.eo, smt := some r } he
          refine ⟨hok.set t e _ he _ r hr ?_, ?_⟩
          · intro kk rr h; cases kk <;> simp [cache.TypeEntry.slot] at h ⊢ <;> simp_all
          · simp [cache.TypeEntry.filled, hs] at hf; omega
        · simp [hs]
          simp only [hset, hlen, true_and]
          have hf := typesFilled_set c.types.val (t.val : Nat) e { eo := e.eo, smt := some r } he
          refine ⟨hok.set t e _ he _ r hr ?_, ?_⟩
          · intro kk rr h; cases kk <;> simp [cache.TypeEntry.slot] at h ⊢ <;> simp_all
          · have : e.smt.isSome = true := by cases h : e.smt <;> simp_all
            simp [cache.TypeEntry.filled, this] at hf; omega
  · simp; exact ⟨hok, hcount⟩

/-- `cached_type`: the terms are untouched, and a result it answers is in
the row of the handle, for that kind. -/
theorem Store.cached_type_spec (s : Store) (hinv : s.Inv) (k : cache.TypeCacheKind) (t : Term) :
    Store.cached_type s k t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧ s'.nodes = s.nodes ∧
      match r with
      | core.result.Result.Ok (some v) => ProgramSem s.nodes.val (typeSemId k) [t] v
      | _ => True ⦄div := by
  unfold Store.cached_type
  rw [Store.view_eq]
  by_cases hv : t.val < s.nodes.length
  · simp only [hv, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step with cache.Caches.type_get_spec s.caches k t as ⟨o, c, hct, hcp, hcs, hres⟩
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    refine ⟨hinv.congr' rfl rfl rfl hct hcp hcs rfl, ⟨List.prefix_refl _, rfl, rfl, le_refl _⟩, trivial, ?_⟩
    cases o with
    | none => trivial
    | some v =>
      obtain ⟨e, he, hslot⟩ := hres v rfl
      exact hinv.cache.types t e he k v hslot
  · simp [hv, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv, Store.Grows.refl s⟩

/-- `cache_type` with a result that is the program's on that term: the
terms are untouched and the invariant holds. -/
theorem Store.cache_type_spec (s : Store) (hinv : s.Inv) (h64 : Platform64)
    (k : cache.TypeCacheKind) (t result : Term)
    (hnew : ProgramSem s.nodes.val (typeSemId k) [t] result) :
    Store.cache_type s k t result ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧ s'.nodes = s.nodes ⦄div := by
  unfold Store.cache_type
  rw [Store.view_eq]
  by_cases hv : t.val < s.nodes.length
  · simp only [hv, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [Store.view_eq]
    by_cases hv2 : result.val < s.nodes.length
    · simp only [hv2, ite_true, Std.bind_ok]
      have hbound : 2 * s.caches.types.length < Usize.max := by
        have h1 := hinv.table.hcache
        have h2 : s.nodes.length < 2 ^ 33 := by have := hinv.table.hmax; scalar_tac
        have h3 : (2 : Nat) ^ 40 ≤ Usize.max := h64
        simp only [alloc.vec.Vec.length] at h1 h2 ⊢
        omega
      step with cache.Caches.type_insert_spec s.caches k t result s.nodes.val hinv.cache.types
        hinv.cache.count hbound hnew as ⟨c, hcp, hcl, hct, hcc⟩
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, hterms, ⟨c1, c2, _, _⟩, hjumps⟩ := hinv
      refine ⟨⟨⟨a1, a2, a3, a4, by simp only [alloc.vec.Vec.length] at hcl ⊢; rw [hcl]; exact a5, a6, a7, a8⟩,
        ⟨hterms.1, hterms.2, hterms.3⟩, ⟨by rw [hcp]; exact c1, by rw [hcp]; exact c2, hct, hcc⟩,
        hjumps⟩,
        ⟨List.prefix_refl _, rfl, rfl, le_refl _⟩, trivial⟩
    · simp [hv2, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact ⟨hinv, Store.Grows.refl s⟩
  · simp [hv, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv, Store.Grows.refl s⟩

end pathos_compiled_checker
