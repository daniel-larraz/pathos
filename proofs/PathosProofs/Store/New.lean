module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Store.Ops

/-!
# A new store has the invariant
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

theorem table.slots_for_one : table.slots_for 1#usize ⦃ r => r.val = 16 ⦄div := by
  unfold table.slots_for table.slots_for_loop
  step*

theorem cache.Caches.new_spec (n : Std.Usize) :
    cache.Caches.new n ⦃ c => c.types.length = 1 ⦄ := by
  unfold cache.Caches.new cache.TypeEntry.empty cache.ProgramCache.new
    cache.CacheStats.Insts.CoreDefaultDefault.default
  step*
  subst y_post
  rfl

/-- A new store has the invariant. -/
theorem Store.new_spec (limits : Limits) : Store.new limits ⦃ s => s.Inv ⦄div := by
  unfold Store.new
  have hdh := dspec_self (Store.data_hash_spec TermData.Stuck)
  step with hdh as ⟨hash, hhash⟩
  step as ⟨y, hy⟩
  step as ⟨y1, hy1⟩
  step with table.slots_for_one as ⟨i, hi⟩
  step as ⟨v, hv, hvlen⟩
  step as ⟨i1, hi1⟩
  step with cache.Caches.new_spec as ⟨c, hc⟩
  step with Store.place_spec as ⟨s, z, x, hx, hz, hfree, hpath, hslots, h1, h2, h3, h4, h5, h6, h7⟩
  have hnodes : s.nodes.val = [TermData.Stuck] := by rw [h1, hy]; rfl
  have hhashes : s.hashes.val = [hash] := by rw [h2, hy1]; rfl
  have hnl : s.nodes.length = 1 := by simp [alloc.vec.Vec.length, hnodes]
  have hsl : s.slots.length = 16 := by
    simp [alloc.vec.Vec.length, hslots, hv, hi]
  constructor
  · constructor
    · omega
    · omega
    · simp [alloc.vec.Vec.length, hnodes, hhashes]
    · rw [hnl]; scalar_tac
    · rw [h3, hc, hnl]
    · rw [hnl, hslots, hhashes]
      have hp0 : Placed [hash] v.val 0 := by rw [hv]; exact Placed.empty _ _
      exact hp0.set (by simpa using hx) hz hfree (by simpa using hpath)
    · intro t ht
      rw [hnl] at ht
      have : t = 0 := by omega
      subst this
      rw [hnodes, hhashes]; exact hhash
    · intro i j hi hj _
      rw [hnl] at hi hj; omega
  · constructor
    · omega
    · rw [hnodes]; rfl
    · intro t ht
      rw [hnl] at ht
      have : t = 0 := by omega
      subst this
      rw [hnodes]; trivial

end pathos_compiled_checker
