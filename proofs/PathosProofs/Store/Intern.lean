module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Trusted
public import PathosProofs.Store.Table
public import PathosProofs.Store.SameData
public import PathosProofs.Store.Hash

/-!
# The store's invariant, and `intern`

`StoreInv` is what makes a handle stand for one term: no two handles have
the same data, and the table finds every term from its data. `intern`
keeps it, and answers the handle of the data it is given.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The invariant of the store's table of terms. -/
structure StoreInv (s : Store) : Prop where
  /-- There are slots (the table is never empty). -/
  hslots : 0 < s.slots.length
  /-- The table is not much larger than what it holds, so doubling it does
  not overflow. -/
  hbound : s.slots.length ≤ 4 * s.nodes.length + 16
  /-- Every term has its hash. -/
  hlen : s.hashes.length = s.nodes.length
  /-- A handle fits in 32 bits, with one value to spare for the slots. -/
  hmax : s.nodes.length ≤ U32.max
  /-- The type cache has no more rows than there are terms. -/
  hcache : s.caches.types.length ≤ s.nodes.length
  /-- The table has every term, and nothing else. -/
  placed : Placed s.hashes.val s.slots.val s.nodes.length
  /-- The hash kept for a term is the hash of its data. -/
  hhash : ∀ t : Nat, t < s.nodes.length →
    Store.data_hash (s.nodes.val[t]!) = ok (s.hashes.val[t]!)
  /-- No two handles have the same data. -/
  nodup : ∀ i j : Nat, i < s.nodes.length → j < s.nodes.length →
    s.nodes.val[i]! = s.nodes.val[j]! → i = j

/-- The rows of the type cache grow by empty rows only, and its counters
stay. -/
def TypesExtend (a b : cache.Caches) : Prop :=
  (∃ k, b.types.val = a.types.val ++ List.replicate k { eo := none, smt := none }) ∧
    b.stats = a.stats

theorem TypesExtend.refl (a : cache.Caches) : TypesExtend a a :=
  ⟨⟨0, by simp⟩, rfl⟩

/-- The store `s'` has the terms of `s` under the same handles. -/
def Store.Extends (s s' : Store) : Prop :=
  s.nodes.val <+: s'.nodes.val ∧ s'.limits = s.limits ∧ s'.calls = s.calls ∧
  s'.depth = s.depth ∧ s'.state_jumps = s.state_jumps ∧
  s'.caches.programs = s.caches.programs ∧ TypesExtend s.caches s'.caches

theorem Placed.append {hashes slots : List Std.U32} {n : Nat} (h : Std.U32)
    (hn : n ≤ hashes.length) (hp : Placed hashes slots n) :
    Placed (hashes ++ [h]) slots n := by
  constructor
  · intro t ht
    obtain ⟨p, hp1, hp2, hp3⟩ := hp.reach t ht
    refine ⟨p, hp1, hp2, ?_⟩
    have : (hashes ++ [h])[t]! = hashes[t]! := by
      simp [List.getElem?_append_left (show t < hashes.length by omega)]
    rw [this]; exact hp3
  · exact hp.valid

@[step]
theorem cache.Caches.push_term_spec (c : cache.Caches) (h : c.types.length < Usize.max) :
    cache.Caches.push_term c ⦃ c' =>
      c'.types.length = c.types.length + 1 ∧
      c'.types.val = c.types.val ++ [{ eo := none, smt := none }] ∧ c'.programs = c.programs ∧
      c'.stats = c.stats ⦄ := by
  unfold cache.Caches.push_term cache.TypeEntry.empty
  step*
  simp [alloc.vec.Vec.length, v_post]

theorem Store.Extends.refl (s : Store) : s.Extends s :=
  ⟨List.prefix_refl _, rfl, rfl, rfl, rfl, rfl, TypesExtend.refl _⟩

/-- `intern` keeps the invariant, keeps every term under its handle, and
answers a handle whose data is the data it was given; the store is as it
was, or has that data as one more term. -/
theorem Store.intern_spec (s : Store) (data : TermData) (hinv : StoreInv s)
    (h64 : Platform64) :
    Store.intern s data ⦃ r s' =>
      StoreInv s' ∧ s.Extends s' ∧
      match r with
      | core.result.Result.Ok t => t.val < s'.nodes.length ∧ s'.nodes.val[t.val]! = data ∧
          (s'.nodes.val = s.nodes.val ∨ s'.nodes.val = s.nodes.val ++ [data])
      | core.result.Result.Err _ => s' = s ⦄div := by
  unfold Store.intern
  have h64' : 2 ^ 40 ≤ Usize.max := h64
  have hdh := dspec_self (Store.data_hash_spec data)
  step with hdh as ⟨hash, hhash⟩
  step with Store.find_spec s data hash (fun td => Store.same_data_spec td data)
    hinv.hslots hinv.hlen hinv.placed as ⟨o, hfound⟩
  cases o with
  | some t =>
    simp only [WP.dspec_ok]
    exact ⟨hinv, Store.Extends.refl s, (hfound.1 t rfl).1, (hfound.1 t rfl).2, Or.inl rfl⟩
  | none =>
    simp only
    step as ⟨i1, hi1⟩
    split
    · simp only [WP.dspec_ok]
      exact ⟨hinv, Store.Extends.refl s, rfl⟩
    · rename_i hlt
      step as ⟨n, hn⟩
      split
      · simp only [WP.dspec_ok]
        exact ⟨hinv, Store.Extends.refl s, rfl⟩
      · rename_i hterms
        have hi1v : i1.val = U32.max := by
          rw [hi1]; simp [core.num.U32.MAX, U32.rMax, U32.max, U32.numBits]
        have hnlt : s.nodes.length < U32.max := by scalar_tac
        have hnv : n.val = s.nodes.length := by rw [hn]; scalar_tac
        have hhl := hinv.hlen
        step as ⟨v, hv⟩
        step as ⟨v1, hv1⟩
        step as ⟨i4, hi4⟩
        have hvlen : v.length = s.nodes.length + 1 := by simp [alloc.vec.Vec.length, hv]
        have hv1len : v1.length = s.nodes.length + 1 := by
          simp [alloc.vec.Vec.length, hv1]; exact hhl
        have hplaced : Placed v1.val s.slots.val s.nodes.length := by
          rw [hv1]; exact hinv.placed.append hash (by rw [← hhl])
        have hself : (if i4 < v.len then
              ({ nodes := v, hashes := v1, slots := s.slots, caches := s.caches, limits := s.limits,
                 calls := s.calls, depth := s.depth, state_jumps := s.state_jumps } : Store).grow
            else
              ({ nodes := v, hashes := v1, slots := s.slots, caches := s.caches, limits := s.limits,
                 calls := s.calls, depth := s.depth, state_jumps := s.state_jumps } : Store).place
                n hash) ⦃ self1 =>
              Placed self1.hashes.val self1.slots.val (s.nodes.length + 1) ∧
              0 < self1.slots.length ∧ self1.slots.length ≤ 4 * (s.nodes.length + 1) + 16 ∧
              self1.nodes = v ∧ self1.hashes = v1 ∧ self1.caches = s.caches ∧
              self1.limits = s.limits ∧ self1.calls = s.calls ∧ self1.depth = s.depth ∧
              self1.state_jumps = s.state_jumps ⦄div := by
          split
          · rename_i hgrow
            have hb := hinv.hbound
            have hs := hinv.hslots
            step with Store.grow_spec as ⟨s1, hp, hl, h1, h2, h3, h4, h5, h6, h7⟩
            refine ⟨?_, ?_, ?_, h1, h2, h3, h4, h5, h6, h7⟩
            · rw [h2] at hp ⊢; rw [← hv1len]; exact hp
            · rw [hl]; omega
            · rw [hl]
              have : s.slots.length / 2 < s.nodes.length + 1 := by scalar_tac
              omega
          · rename_i hnogrow
            have hb := hinv.hbound
            have hs := hinv.hslots
            step with Store.place_spec as ⟨s1, z, x, hx, hz, hfree, hpath, hslots, h1, h2, h3, h4, h5, h6, h7⟩
            refine ⟨?_, ?_, ?_, h1, h2, h3, h4, h5, h6, h7⟩
            · rw [h2, hslots]
              refine hplaced.set (by rw [hx, hnv]) hz hfree ?_
              have : (v1.val[s.nodes.length]! : Std.U32) = hash := by
                rw [hv1, ← hhl]; simp
              rw [this]; exact hpath
            · simp [alloc.vec.Vec.length, hslots]; exact hs
            · simp [alloc.vec.Vec.length, hslots]; simp [alloc.vec.Vec.length] at hb; omega
        step with hself as ⟨self1, hp, hpos, hbnd, e1, e2, e3, e4, e5, e6, e7⟩
        have hc := hinv.hcache
        step as ⟨c, hc', hcv, hcp, hcs⟩
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        have hnodes : ∀ t : Nat, t < s.nodes.length → v.val[t]! = s.nodes.val[t]! := by
          intro t ht; rw [hv]; simp [List.getElem?_append_left ht]
        have hlast : v.val[s.nodes.length]! = data := by rw [hv]; simp
        have hhashes : ∀ t : Nat, t < s.nodes.length → v1.val[t]! = s.hashes.val[t]! := by
          intro t ht; rw [hv1]; simp [List.getElem?_append_left (show t < s.hashes.val.length by rw [← alloc.vec.Vec.length, hhl]; exact ht)]
        have hlasth : v1.val[s.nodes.length]! = hash := by rw [hv1, ← hhl]; simp
        have hfresh : ∀ t : Nat, t < s.nodes.length → s.nodes.val[t]! ≠ data := by
          intro t ht hd
          refine hfound.2 rfl t ht ?_ hd
          have := hinv.hhash t ht
          rw [hd, hhash] at this
          simpa using this.symm
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · constructor
          · exact hpos
          · simp only [e1]; rw [hvlen]; exact hbnd
          · simp only [e1, e2]; rw [hvlen, hv1len]
          · simp only [e1]; rw [hvlen]; omega
          · simp only [e1]; rw [hvlen, hc', e3]; omega
          · simp only [e1]; rw [hvlen]; exact hp
          · simp only [e1, e2]
            intro t ht
            rw [hvlen] at ht
            by_cases htn : t = s.nodes.length
            · subst htn; rw [hlast, hlasth]; exact hhash
            · have ht' : t < s.nodes.length := by omega
              rw [hnodes t ht', hhashes t ht']; exact hinv.hhash t ht'
          · simp only [e1]
            intro i j hi hj hij
            rw [hvlen] at hi hj
            by_cases hin : i = s.nodes.length <;> by_cases hjn : j = s.nodes.length
            · omega
            · subst hin
              have hj' : j < s.nodes.length := by omega
              rw [hlast, hnodes j hj'] at hij
              exact absurd hij.symm (hfresh j hj')
            · subst hjn
              have hi' : i < s.nodes.length := by omega
              rw [hlast, hnodes i hi'] at hij
              exact absurd hij (hfresh i hi')
            · have hi' : i < s.nodes.length := by omega
              have hj' : j < s.nodes.length := by omega
              rw [hnodes i hi', hnodes j hj'] at hij
              exact hinv.nodup i j hi' hj' hij
        · refine ⟨?_, e4, e5, e6, e7, by rw [hcp, e3], ⟨⟨1, by rw [hcv, e3]; rfl⟩, by rw [hcs, e3]⟩⟩
          simp only [e1]; rw [hv]; exact List.prefix_append _ _
        · simp only [e1]; rw [hvlen, hnv]; omega
        · simp only [e1]; rw [hnv]; exact hlast
        · simp only [e1]; exact Or.inr hv

end pathos_compiled_checker
