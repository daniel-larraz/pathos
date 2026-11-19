module
public import MiniChecker
public import PathosProofs.Util

/-!
# The table of terms: searching and placing

`Store` finds a term from its data in `slots`, an open-addressed table of
handles (a slot is 0 or a handle plus one), searched from the slot the
data's hash names through the slots that are taken. This file is about the
two loops that walk it, `Store.place` and `Store.find`, as walks: `Path`.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- From slot `i` the search reaches slot `j` through slots that are taken
(`j` itself is not looked at). -/
inductive Path (slots : List Std.U32) (mask : Nat) : Nat → Nat → Prop where
  | here (i : Nat) : Path slots mask i i
  | step (i j : Nat) :
      slots[i]! ≠ 0#u32 → Path slots mask ((i + 1) &&& mask) j → Path slots mask i j

/-- Writing into a free slot does not change the paths there were. -/
theorem Path.set_free {slots : List Std.U32} {mask i j : Nat} (z : Nat) (x : Std.U32)
    (hz : slots[z]! = 0#u32) (h : Path slots mask i j) :
    Path (slots.set z x) mask i j := by
  induction h with
  | here i => exact Path.here i
  | step i j hi _ ih =>
    refine Path.step i j ?_ ih
    have hne : z ≠ i := by
      intro heq; subst heq; exact hi hz
    simpa [List.getElem?_set_ne hne] using hi

theorem Store.place_loop_spec (v : alloc.vec.Vec Std.U32) (mask i : Std.Usize)
    (hmask : mask.val < v.length) (hi : i.val < v.length) :
    Store.place_loop v mask i ⦃ j =>
      Path v.val mask.val i.val j.val ∧ j.val < v.length ∧ v.val[j.val]! = 0#u32 ⦄div := by
  revert i
  apply Store.place_loop.fixpoint_induct v mask
    (motive := fun f => ∀ i : Std.Usize, i.val < v.length →
      f i ⦃ j => Path v.val mask.val i.val j.val ∧ j.val < v.length ∧ v.val[j.val]! = 0#u32 ⦄div)
  · prove_adm
  · intro place_loop ih i hi
    simp only
    step
    split
    · step
      step
      have h3 : i3.val < v.length := by
        have : i3.val ≤ mask.val := by rw [i3_post]; simp; exact Nat.and_le_right
        omega
      step with ih
      refine ⟨Path.step _ _ ?_ ?_, j_post1, j_post2⟩
      · simp_all
      · have : (i.val + 1) &&& mask.val = i3.val := by rw [i3_post]; simp [i2_post]
        rw [this]; exact j_post
    · simp only [WP.dspec_ok]
      refine ⟨Path.here _, hi, ?_⟩
      simp_all
      scalar_tac

/-- `place` writes `t + 1` into the first free slot on the path from the
slot the hash names, and changes nothing else. -/
theorem Store.place_spec (s : Store) (t : Term) (hash : Std.U32)
    (hlen : 0 < s.slots.length) (ht : t.val < U32.max) :
    Store.place s t hash ⦃ s' => ∃ (z : Nat) (x : Std.U32),
      x.val = t.val + 1 ∧ z < s.slots.length ∧ s.slots.val[z]! = 0#u32 ∧
      Path s.slots.val (s.slots.length - 1) (hash.val &&& (s.slots.length - 1)) z ∧
      s'.slots.val = s.slots.val.set z x ∧
      s'.nodes = s.nodes ∧ s'.hashes = s.hashes ∧ s'.caches = s.caches ∧
      s'.limits = s.limits ∧ s'.calls = s.calls ∧ s'.depth = s.depth ∧
      s'.state_jumps = s.state_jumps ⦄div := by
  unfold Store.place
  step as ⟨mask, hmask⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hmask' : mask.val < s.slots.length := by scalar_tac
  have hi2' : i2.val = hash.val &&& (s.slots.length - 1) := by
    rw [hi2]; simp [hi1, hmask]
  have hi2lt : i2.val < s.slots.length := by
    have : i2.val ≤ mask.val := by rw [hi2]; simp; exact Nat.and_le_right
    omega
  step with Store.place_loop_spec as ⟨i3, hpath, hi3, hfree⟩
  step as ⟨i4, hi4⟩
  step as ⟨old, back, hold, hback⟩
  simp only [WP.dspec_ok]
  refine ⟨i3.val, i4, by scalar_tac, hi3, hfree, ?_, ?_⟩
  · rw [← hi2']
    have : s.slots.length - 1 = mask.val := by scalar_tac
    rw [this]; exact hpath
  · simp [hback]

/-- The table has term `t`: the search from the slot that `t`'s hash names
comes to a slot holding `t`. -/
def Reaches (hashes slots : List Std.U32) (t : Nat) : Prop :=
  ∃ p, p < slots.length ∧ (slots[p]! : Std.U32).val = t + 1 ∧
    Path slots (slots.length - 1) ((hashes[t]! : Std.U32).val &&& (slots.length - 1)) p

/-- The table has the first `n` terms and nothing else. -/
structure Placed (hashes slots : List Std.U32) (n : Nat) : Prop where
  reach : ∀ t : Nat, t < n → Reaches hashes slots t
  valid : ∀ p : Nat, slots[p]! ≠ 0#u32 → (slots[p]! : Std.U32).val ≤ n

theorem Reaches.set_free {hashes slots : List Std.U32} {t : Nat} (z : Nat) (x : Std.U32)
    (hz : slots[z]! = 0#u32) (h : Reaches hashes slots t) :
    Reaches hashes (slots.set z x) t := by
  obtain ⟨p, hp, hval, hpath⟩ := h
  have hne : z ≠ p := by
    intro heq; subst heq; rw [hz] at hval; simp at hval
  refine ⟨p, by simpa using hp, ?_, ?_⟩
  · simpa [List.getElem?_set_ne hne] using hval
  · simpa using hpath.set_free z x hz

/-- Placing the next term keeps the table. -/
theorem Placed.set {hashes slots : List Std.U32} {n z : Nat} {x : Std.U32}
    (h : Placed hashes slots n) (hx : x.val = n + 1) (hzlt : z < slots.length)
    (hz : slots[z]! = 0#u32)
    (hpath : Path slots (slots.length - 1) ((hashes[n]! : Std.U32).val &&& (slots.length - 1)) z) :
    Placed hashes (slots.set z x) (n + 1) := by
  constructor
  · intro t ht
    by_cases htn : t = n
    · subst htn
      refine ⟨z, by simpa using hzlt, ?_, ?_⟩
      · simp [hzlt, hx]
      · simpa using hpath.set_free z x hz
    · exact (h.reach t (by omega)).set_free z x hz
  · intro p hp
    by_cases hpz : z = p
    · subst hpz; simp [hzlt, hx]
    · have : (slots.set z x)[p]! = slots[p]! := by simp [List.getElem?_set_ne hpz]
      rw [this] at hp ⊢
      have := h.valid p hp
      omega

/-- The loop of `grow`: every term from `t` on is placed. -/
theorem Store.grow_loop_spec (s : Store) (t : Std.Usize)
    (hlen : 0 < s.slots.length) (hmax : s.hashes.length ≤ U32.max)
    (ht : t.val ≤ s.hashes.length)
    (h : Placed s.hashes.val s.slots.val t.val) :
    Store.grow_loop s t ⦃ nodes hashes slots caches limits calls depth jumps =>
      Placed hashes.val slots.val hashes.length ∧ slots.length = s.slots.length ∧
      nodes = s.nodes ∧ hashes = s.hashes ∧ caches = s.caches ∧ limits = s.limits ∧
      calls = s.calls ∧ depth = s.depth ∧ jumps = s.state_jumps ⦄div := by
  revert s t
  apply Store.grow_loop.fixpoint_induct
    (motive := fun f => ∀ (s : Store) (t : Std.Usize),
      0 < s.slots.length → s.hashes.length ≤ U32.max → t.val ≤ s.hashes.length →
      Placed s.hashes.val s.slots.val t.val →
      f s t ⦃ nodes hashes slots caches limits calls depth jumps =>
        Placed hashes.val slots.val hashes.length ∧ slots.length = s.slots.length ∧
        nodes = s.nodes ∧ hashes = s.hashes ∧ caches = s.caches ∧ limits = s.limits ∧
        calls = s.calls ∧ depth = s.depth ∧ jumps = s.state_jumps ⦄div)
  · prove_adm
  · intro grow_loop ih s t hlen hmax ht h
    simp only
    split
    · rename_i hlt
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi1v : i1.val = t.val := by rw [hi1]; scalar_tac
      step with Store.place_spec as ⟨s1, z, x, hx, hz, hfree, hpath, hslots, hn, hh, hc, hl, hca, hd, hj⟩
      step as ⟨t1, ht1⟩
      have hlen1 : s1.slots.length = s.slots.length := by
        simp only [alloc.vec.Vec.length, hslots, List.length_set]
      have hp1 : Placed s1.hashes.val s1.slots.val t1.val := by
        rw [hh, hslots, ht1]
        refine h.set (by rw [hx, hi1v]) hz hfree ?_
        have hlt' : t.val < s.hashes.val.length := by scalar_tac
        have : (s.hashes.val[t.val]! : Std.U32) = i2 := by simp [hi2, hlt']
        rw [this]; exact hpath
      step with ih as ⟨nodes, hashes, slots, caches, limits, calls, depth, jumps, hpost⟩
      simp_all
    · rename_i hge
      simp only [WP.dspec_ok]
      have : t.val = s.hashes.length := by scalar_tac
      rw [this] at h
      simp [h]

theorem Placed.empty (hashes : List Std.U32) (n : Nat) :
    Placed hashes (List.replicate n 0#u32) 0 := by
  constructor
  · intro t ht; omega
  · intro p hp
    exfalso; apply hp
    by_cases h : p < n <;> simp [h]
    rfl

/-- `grow` doubles the table and places every term again. -/
theorem Store.grow_spec (s : Store)
    (hlen : 0 < s.slots.length) (hmax : s.hashes.length ≤ U32.max)
    (hdouble : s.slots.length * 2 ≤ Usize.max) :
    Store.grow s ⦃ s' =>
      Placed s'.hashes.val s'.slots.val s'.hashes.length ∧
      s'.slots.length = s.slots.length * 2 ∧
      s'.nodes = s.nodes ∧ s'.hashes = s.hashes ∧ s'.caches = s.caches ∧
      s'.limits = s.limits ∧ s'.calls = s.calls ∧ s'.depth = s.depth ∧
      s'.state_jumps = s.state_jumps ⦄div := by
  unfold Store.grow
  step as ⟨i1, hi1⟩
  step as ⟨v, hv, hvlen⟩
  step with Store.grow_loop_spec as ⟨nodes, hashes, slots, caches, limits, calls, depth, jumps, hpost⟩
  · simp only [hv]; exact Placed.empty _ _
  · simp_all

instance : Inhabited TermData := ⟨TermData.Stuck⟩

/-- What `find` answers: a term with the data, or that no term with that
hash has it. -/
def Found (nodes : List TermData) (hashes : List Std.U32) (data : TermData)
    (hash : Std.U32) (found : Option Term) : Prop :=
  (∀ t : Term, found = some t → t.val < nodes.length ∧ nodes[t.val]! = data) ∧
  (found = none → ∀ t : Nat, t < nodes.length → hashes[t]! = hash → nodes[t]! ≠ data)

/-- While `find` searches from slot `i`: every term with the data and the
hash is still ahead. -/
def Ahead (nodes : List TermData) (hashes slots : List Std.U32) (data : TermData)
    (hash : Std.U32) (mask i : Nat) : Prop :=
  ∀ t : Nat, t < nodes.length → hashes[t]! = hash → nodes[t]! = data →
    ∃ p, (slots[p]! : Std.U32).val = t + 1 ∧ Path slots mask i p

theorem Store.find_loop_spec (nodes : alloc.vec.Vec TermData)
    (hashes slots : alloc.vec.Vec Std.U32) (data : TermData) (hash : Std.U32)
    (mask : Std.Usize)
    (hsd : ∀ td, Store.same_data td data ⦃ b => (b = true ↔ td = data) ⦄div)
    (hmask : mask.val < slots.length) (hlen : hashes.length = nodes.length)
    (hvalid : ∀ p : Nat, slots.val[p]! ≠ 0#u32 → (slots.val[p]! : Std.U32).val ≤ nodes.length)
    (i : Std.Usize) (found : Option Term) (searching : Bool)
    (hi : i.val < slots.length)
    (h : if searching then found = none ∧ Ahead nodes.val hashes.val slots.val data hash mask.val i.val
         else Found nodes.val hashes.val data hash found) :
    Store.find_loop nodes hashes slots data hash mask i found searching
      ⦃ r => Found nodes.val hashes.val data hash r ⦄div := by
  revert i found searching
  apply Store.find_loop.fixpoint_induct nodes hashes slots data hash mask
    (motive := fun f => ∀ (i : Std.Usize) (found : Option Term) (searching : Bool),
      i.val < slots.length →
      (if searching then found = none ∧ Ahead nodes.val hashes.val slots.val data hash mask.val i.val
         else Found nodes.val hashes.val data hash found) →
      f i found searching ⦃ r => Found nodes.val hashes.val data hash r ⦄div)
  · prove_adm
  · intro find_loop ih i found searching hi h
    simp only
    split
    · rename_i hs
      simp only [hs, ite_true] at h
      obtain ⟨hnone, hahead⟩ := h
      step as ⟨s, hs'⟩
      have hsi : slots.val[i.val]! = s := by simp [hs', hi]
      have hnext : ∀ (i4 : Std.Usize) (i3 : Std.Usize), i3.val = i.val + 1 →
          i4.val = (i3 &&& mask).val → i4.val < slots.length ∧ i4.val = (i.val + 1) &&& mask.val := by
        intro i4 i3 h3 h4
        have : i4.val = (i.val + 1) &&& mask.val := by rw [h4]; simp [h3]
        refine ⟨?_, this⟩
        have : i4.val ≤ mask.val := by rw [this]; exact Nat.and_le_right
        omega
      split
      · rename_i hzero
        apply ih i found false hi
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨by intro t ht; simp [hnone] at ht, ?_⟩
        intro _ t ht hh hd
        obtain ⟨p, hp, hpath⟩ := hahead t ht hh hd
        cases hpath with
        | here => rw [hsi, hzero] at hp; simp at hp
        | step _ _ hne _ => rw [hsi, hzero] at hne; simp at hne
      · rename_i hnz
        have hsv : s.val ≤ nodes.length := by
          have := hvalid i.val (by rw [hsi]; exact hnz)
          rw [hsi] at this; exact this
        have hspos : 0 < s.val := by scalar_tac
        step as ⟨i1, hi1⟩
        step as ⟨t, ht⟩
        have htv : t.val = s.val - 1 := by rw [ht]; scalar_tac
        have htlt : t.val < nodes.val.length := by scalar_tac
        have hhlt : t.val < hashes.val.length := by scalar_tac
        step as ⟨i2, hi2⟩
        have hstep : ∀ i4 : Std.Usize, i4.val = (i.val + 1) &&& mask.val →
            (nodes.val[t.val]! = data → hashes.val[t.val]! ≠ hash) →
            Ahead nodes.val hashes.val slots.val data hash mask.val i4.val := by
          intro i4 h4 hne t' ht' hh hd
          obtain ⟨p, hp, hpath⟩ := hahead t' ht' hh hd
          cases hpath with
          | here =>
            rw [hsi] at hp
            have : t' = t.val := by omega
            subst this
            exact absurd hh (hne hd)
          | step _ _ _ hrest => exact ⟨p, hp, h4 ▸ hrest⟩
        split
        · rename_i heq
          step as ⟨td, htd⟩
          step with hsd as ⟨b, hb⟩
          split
          · rename_i hbt
            apply ih i (some i1) false hi
            simp only [Bool.false_eq_true, ite_false]
            refine ⟨?_, by simp⟩
            intro t' ht'
            simp at ht'
            subst ht'
            have : i1.val = t.val := by scalar_tac
            rw [this]
            refine ⟨htlt, ?_⟩
            have := hb.mp hbt
            rw [← this, htd]; exact getElem!_eq _ _ htlt
          · rename_i hbf
            step as ⟨i3, hi3⟩
            step as ⟨i4, hi4⟩
            obtain ⟨h4lt, h4⟩ := hnext i4 i3 hi3 hi4
            apply ih i4 found searching h4lt
            simp only [hs, ite_true]
            refine ⟨hnone, hstep i4 h4 ?_⟩
            intro hd
            exfalso; apply hbf; apply hb.mpr
            rw [htd, ← hd]; exact (getElem!_eq _ _ htlt).symm
        · rename_i hneq
          step as ⟨i3, hi3⟩
          step as ⟨i4, hi4⟩
          obtain ⟨h4lt, h4⟩ := hnext i4 i3 hi3 hi4
          apply ih i4 found searching h4lt
          simp only [hs, ite_true]
          refine ⟨hnone, hstep i4 h4 ?_⟩
          intro _ hh
          apply hneq
          rw [hi2, ← hh]; exact (getElem!_eq _ _ hhlt).symm
    · rename_i hs
      simp only [hs] at h
      simp only [WP.dspec_ok]
      simpa using h

/-- `find` gives a term with the data, or `none` when no term with that
hash has the data. -/
theorem Store.find_spec (s : Store) (data : TermData) (hash : Std.U32)
    (hsd : ∀ td, Store.same_data td data ⦃ b => (b = true ↔ td = data) ⦄div)
    (hslots : 0 < s.slots.length) (hlen : s.hashes.length = s.nodes.length)
    (hp : Placed s.hashes.val s.slots.val s.nodes.length) :
    Store.find s data hash ⦃ r => Found s.nodes.val s.hashes.val data hash r ⦄div := by
  unfold Store.find
  step as ⟨mask, hmask⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hmask' : mask.val = s.slots.length - 1 := by scalar_tac
  have hi2' : i2.val = hash.val &&& (s.slots.length - 1) := by
    rw [hi2]; simp [hi1, hmask]
  have hi2lt : i2.val < s.slots.length := by
    have : i2.val ≤ mask.val := by rw [hi2]; simp; exact Nat.and_le_right
    omega
  apply Store.find_loop_spec s.nodes s.hashes s.slots data hash mask hsd (by omega) hlen
    hp.valid i2 none true hi2lt
  simp only [ite_true, true_and]
  intro t ht hh _
  obtain ⟨p, _, hval, hpath⟩ := hp.reach t ht
  refine ⟨p, hval, ?_⟩
  rw [hmask', hi2', ← hh]; exact hpath

end pathos_compiled_checker
