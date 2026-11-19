module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Store.Table

/-!
# The cache of program results, as a table

`ProgramCache` keeps the results of programs by program and arguments, in
a second open-addressed table. What is proved of it is what the checker's
correctness needs, and no more:

* its operations do not panic on a table that is well formed, and keep it
  well formed;
* what `get` answers is the result of an entry with that program and
  those arguments;
* `insert` adds one entry, for its program, arguments and result, or
  leaves the entries as they were.

That `get` finds every entry is not proved, and not needed: a cache that
misses is slower, not wrong.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

instance : Inhabited cache.ProgramEntry :=
  ⟨{ program := 0#u32, args := alloc.vec.Vec.new Term, result := 0#u32 }⟩

/-- The table of a program cache is well formed: a slot names an entry. -/
structure CacheWf (pc : cache.ProgramCache) : Prop where
  valid : ∀ p : Nat, pc.slots.val[p]! ≠ 0#u32 →
    (pc.slots.val[p]! : Std.U32).val ≤ pc.entries.length
  hmax : pc.entries.length ≤ U32.max

theorem cache.ProgramCache.hash_loop_spec (args : Slice Term) (h : Std.U64) (i : Std.Usize) :
    cache.ProgramCache.hash_loop args h i ⦃ _ => True ⦄div := by
  revert h i
  apply cache.ProgramCache.hash_loop.fixpoint_induct args
    (motive := fun f => ∀ (h : Std.U64) (i : Std.Usize), f h i ⦃ _ => True ⦄div)
  · prove_adm
  · intro loop ih h i
    simp only
    split
    · step*
    · simp

@[step]
theorem cache.ProgramCache.hash_spec (program : cache.ProgramId) (args : Slice Term) :
    cache.ProgramCache.hash program args ⦃ _ => True ⦄div := by
  unfold cache.ProgramCache.hash
  step
  step
  step with cache.ProgramCache.hash_loop_spec
  step*

theorem cache.ProgramCache.matches_loop_spec (v : alloc.vec.Vec Term) (args : Slice Term)
    (hlen : v.length = args.length) (i : Std.Usize) :
    cache.ProgramCache.matches_loop v args i ⦃ b =>
      b = true → ∀ j : Nat, i.val ≤ j → j < args.length → v.val[j]! = args.val[j]! ⦄div := by
  revert i
  apply cache.ProgramCache.matches_loop.fixpoint_induct v args
    (motive := fun f => ∀ i : Std.Usize, f i ⦃ b =>
      b = true → ∀ j : Nat, i.val ≤ j → j < args.length → v.val[j]! = args.val[j]! ⦄div)
  · prove_adm
  · intro loop ih i
    simp only
    split
    · rename_i hlt
      have hilt : i.val < args.val.length := by scalar_tac
      have hilt' : i.val < v.val.length := by
        have : v.val.length = args.val.length := hlen
        omega
      step as ⟨t, ht⟩
      step as ⟨t1, ht1⟩
      split
      · simp
      · rename_i heq
        step as ⟨i2, hi2⟩
        apply WP.dspec_mono (ih i2)
        intro b hb hbt j hj hjl
        by_cases hji : j = i.val
        · subst hji
          rw [getElem!_eq _ _ hilt, getElem!_eq _ _ hilt', ← ht, ← ht1]
          simp at heq; scalar_tac
        · exact hb hbt j (by omega) hjl
    · rename_i hge
      simp only [WP.dspec_ok]
      intro _ j hj hjl
      exfalso; scalar_tac

/-- `matches` answers `true` only for an entry of that program with those
arguments. -/
@[step]
theorem cache.ProgramCache.matches_spec (e : cache.ProgramEntry) (program : cache.ProgramId)
    (args : Slice Term) :
    cache.ProgramCache.matches e program args ⦃ b =>
      b = true → e.program = program ∧ e.args.val = args.val ⦄div := by
  unfold cache.ProgramCache.matches
  dsimp only
  split
  · simp
  · rename_i hp
    split
    · simp
    · rename_i hl
      have hlen : e.args.length = args.length := by simp at hl; scalar_tac
      apply WP.dspec_mono (cache.ProgramCache.matches_loop_spec e.args args hlen 0#usize)
      intro b hb hbt
      refine ⟨by simp at hp; scalar_tac, ?_⟩
      apply List.ext_getElem! hlen
      intro j
      by_cases hj : j < args.length
      · exact hb hbt j (by simp) hj
      · have h1 : ¬ j < args.val.length := hj
        have h2 : ¬ j < e.args.val.length := by
          have : e.args.val.length = args.val.length := hlen
          omega
        simp [h1, h2]

/-- What `find` answers: a slot, and if it is taken, by an entry of that
program with those arguments. -/
def CacheHit (pc : cache.ProgramCache) (program : cache.ProgramId) (args : Slice Term)
    (slot : Nat) : Prop :=
  slot < pc.slots.length ∧
  (pc.slots.val[slot]! ≠ 0#u32 →
    (pc.entries.val[(pc.slots.val[slot]! : Std.U32).val - 1]!).program = program ∧
    (pc.entries.val[(pc.slots.val[slot]! : Std.U32).val - 1]!).args.val = args.val)

theorem cache.ProgramCache.find_loop_spec (pc : cache.ProgramCache) (hwf : CacheWf pc)
    (program : cache.ProgramId) (args : Slice Term) (mask : Std.Usize)
    (hmask : mask.val < pc.slots.length) (slot : Std.Usize) (hslot : slot.val < pc.slots.length) :
    cache.ProgramCache.find_loop pc.entries pc.slots program args mask slot ⦃ r =>
      CacheHit pc program args r.val ⦄div := by
  revert slot
  apply cache.ProgramCache.find_loop.fixpoint_induct pc.entries pc.slots program args mask
    (motive := fun f => ∀ slot : Std.Usize, slot.val < pc.slots.length →
      f slot ⦃ r => CacheHit pc program args r.val ⦄div)
  · prove_adm
  · intro loop ih slot hslot
    simp only
    step as ⟨index, hindex⟩
    have hidx : pc.slots.val[slot.val]! = index := by rw [hindex]; exact getElem!_eq _ _ hslot
    split
    · rename_i hz
      simp only [WP.dspec_ok]
      exact ⟨hslot, fun h => absurd (hidx.trans hz) h⟩
    · rename_i hnz
      have hv := hwf.valid slot.val (by rw [hidx]; exact hnz)
      rw [hidx] at hv
      have hpos : 0 < index.val := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = index.val - 1 := by rw [hi1]; scalar_tac
      have hi1lt : i1.val < pc.entries.val.length := by
        have : pc.entries.val.length = pc.entries.length := rfl
        omega
      step as ⟨pe, hpe⟩
      step as ⟨b, hb⟩
      split
      · rename_i hbt
        simp only [WP.dspec_ok]
        refine ⟨hslot, fun _ => ?_⟩
        rw [hidx, ← hi1v, getElem!_eq _ _ hi1lt, ← hpe]
        exact hb hbt
      · step as ⟨i2, hi2⟩
        step as ⟨slot1, hs1⟩
        apply ih slot1
        have : slot1.val ≤ mask.val := by rw [hs1]; simp; exact Nat.and_le_right
        omega

/-- `find` on a table with slots. -/
theorem cache.ProgramCache.find_spec (pc : cache.ProgramCache) (hwf : CacheWf pc)
    (hne : 0 < pc.slots.length) (program : cache.ProgramId) (args : Slice Term) :
    cache.ProgramCache.find pc program args ⦃ r => CacheHit pc program args r.val ⦄div := by
  unfold cache.ProgramCache.find
  step as ⟨mask, hmask⟩
  step as ⟨i1⟩
  step as ⟨i2, hi2⟩
  step as ⟨slot, hslot⟩
  have hm : mask.val < pc.slots.length := by scalar_tac
  apply cache.ProgramCache.find_loop_spec pc hwf program args mask hm slot
  have : slot.val ≤ mask.val := by rw [hslot]; simp; exact Nat.and_le_right
  omega

/-- What `get` answers is the result of an entry with that program and
those arguments. -/
theorem cache.ProgramCache.get_spec (pc : cache.ProgramCache) (hwf : CacheWf pc)
    (program : cache.ProgramId) (args : Slice Term) :
    cache.ProgramCache.get pc program args ⦃ r =>
      ∀ v, r = some v → ∃ e, e ∈ pc.entries.val ∧ e.program = program ∧
        e.args.val = args.val ∧ e.result = v ⦄div := by
  unfold cache.ProgramCache.get
  step as ⟨b, hb⟩
  split
  · simp
  · rename_i hne
    have hpos : 0 < pc.slots.length := by
      simp [hb] at hne; exact List.length_pos_of_ne_nil hne
    step with cache.ProgramCache.find_spec pc hwf hpos as ⟨slot, hhit'⟩
    obtain ⟨hlt, hhit⟩ := hhit'
    step as ⟨index, hindex⟩
    have hidx : pc.slots.val[slot.val]! = index := by rw [hindex]; exact getElem!_eq _ _ hlt
    split
    · simp
    · rename_i hnz
      have hv := hwf.valid slot.val (by rw [hidx]; exact hnz)
      rw [hidx] at hv
      have hpos' : 0 < index.val := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = index.val - 1 := by rw [hi1]; scalar_tac
      have hi1lt : i1.val < pc.entries.val.length := by
        have : pc.entries.val.length = pc.entries.length := rfl
        omega
      step as ⟨pe, hpe⟩
      simp only [WP.dspec_ok]
      intro v hv'
      have hh := hhit (by rw [hidx]; exact hnz)
      rw [hidx, ← hi1v, getElem!_eq _ _ hi1lt, ← hpe] at hh
      refine ⟨pe, ?_, hh.1, hh.2, by simpa using hv'⟩
      rw [hpe]; exact List.getElem_mem hi1lt

/-- Every slot names an entry among the first `n`. -/
def SlotsValid (slots : List Std.U32) (n : Nat) : Prop :=
  ∀ p : Nat, slots[p]! ≠ 0#u32 → (slots[p]! : Std.U32).val ≤ n

theorem SlotsValid.set {slots : List Std.U32} {n : Nat} (h : SlotsValid slots n) (z : Nat)
    {x : Std.U32} (hx : x.val ≤ n) : SlotsValid (slots.set z x) n := by
  intro p hp
  by_cases hpz : z = p
  · subst hpz
    by_cases hz : z < slots.length
    · simp [hz]; exact hx
    · have : (slots.set z x)[z]! = slots[z]! := by simp [hz]
      rw [this] at hp ⊢; exact h z hp
  · have : (slots.set z x)[p]! = slots[p]! := by simp [List.getElem?_set_ne hpz]
    rw [this] at hp ⊢; exact h p hp

theorem SlotsValid.mono {slots : List Std.U32} {n m : Nat} (h : SlotsValid slots n)
    (hnm : n ≤ m) : SlotsValid slots m :=
  fun p hp => Nat.le_trans (h p hp) hnm

theorem SlotsValid.replicate (k n : Nat) : SlotsValid (List.replicate k 0#u32) n := by
  intro p hp
  exfalso; apply hp
  by_cases h : p < k <;> simp [h]
  rfl

theorem cache.ProgramCache.grow_loop0_loop0_spec (m : Std.Usize)
    (slots : alloc.vec.Vec Std.U32) (hm : m.val < slots.length) (slot : Std.Usize)
    (hslot : slot.val < slots.length) :
    cache.ProgramCache.grow_loop0_loop0 m slots slot ⦃ r => r.val < slots.length ⦄div := by
  revert slot
  apply cache.ProgramCache.grow_loop0_loop0.fixpoint_induct m slots
    (motive := fun f => ∀ slot : Std.Usize, slot.val < slots.length →
      f slot ⦃ r => r.val < slots.length ⦄div)
  · prove_adm
  · intro loop ih slot hslot
    simp only
    step as ⟨i1, hi1⟩
    split
    · step as ⟨i2, hi2⟩
      step as ⟨slot1, hs1⟩
      apply ih slot1
      have : slot1.val ≤ m.val := by rw [hs1]; simp; exact Nat.and_le_right
      scalar_tac
    · simp only [WP.dspec_ok]; exact hslot

theorem cache.ProgramCache.grow_loop1_loop0_spec (size : Std.Usize)
    (slots : alloc.vec.Vec Std.U32) (hsize : size.val = slots.length) (slot : Std.Usize)
    (hslot : slot.val < slots.length) :
    cache.ProgramCache.grow_loop1_loop0 size slots slot ⦃ r => r.val < slots.length ⦄div := by
  revert slot
  apply cache.ProgramCache.grow_loop1_loop0.fixpoint_induct size slots
    (motive := fun f => ∀ slot : Std.Usize, slot.val < slots.length →
      f slot ⦃ r => r.val < slots.length ⦄div)
  · prove_adm
  · intro loop ih slot hslot
    simp only
    step as ⟨i1, hi1⟩
    split
    · step as ⟨i2, hi2⟩
      step as ⟨m, hm⟩
      step as ⟨slot1, hs1⟩
      apply ih slot1
      have : slot1.val ≤ m.val := by rw [hs1]; simp; exact Nat.and_le_right
      scalar_tac
    · simp only [WP.dspec_ok]; exact hslot

theorem cache.ProgramCache.grow_loop0_spec (v : alloc.vec.Vec cache.ProgramEntry) 
    (hmax : v.length ≤ U32.max) (slots : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (hlen : slots.length = 16) (hi : i.val ≤ v.length) (hvalid : SlotsValid slots.val v.length) :
    cache.ProgramCache.grow_loop0 v  slots i ⦃ slots' =>
      slots'.length = slots.length ∧ SlotsValid slots'.val v.length ⦄div := by
  revert slots i
  apply cache.ProgramCache.grow_loop0.fixpoint_induct v 
    (motive := fun f => ∀ (slots : alloc.vec.Vec Std.U32) (i : Std.Usize),
      slots.length = 16 → i.val ≤ v.length → SlotsValid slots.val v.length →
      f slots i ⦃ slots' =>
        slots'.length = slots.length ∧ SlotsValid slots'.val v.length ⦄div)
  · prove_adm
  · intro loop ih slots i hlen hi hvalid
    simp only
    split
    · rename_i hlt
      step as ⟨entry, hentry⟩
      step as ⟨i2⟩
      step as ⟨i3, hi3⟩
      step as ⟨m, hm⟩
      step as ⟨slot, hslot⟩
      have hslotlt : slot.val < slots.length := by
        have : slot.val ≤ m.val := by rw [hslot]; simp; exact Nat.and_le_right
        scalar_tac
      step with cache.ProgramCache.grow_loop0_loop0_spec m slots (by scalar_tac) slot hslotlt as ⟨slot1, hslot1⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨old, back, hold, hback⟩
      step as ⟨i7, hi7⟩
      have hset : (back i6).val = slots.val.set slot1.val i6 := by simp [hback]
      have hlen' : (back i6).length = slots.length := by
        simp [alloc.vec.Vec.length, hset]
      have hi6v : i6.val ≤ v.length := by scalar_tac
      apply WP.dspec_mono (ih (back i6) i7 (by rw [hlen']; exact hlen) (by scalar_tac)
        (by rw [hset]; exact hvalid.set _ hi6v))
      intro slots' ⟨h1, h2⟩
      exact ⟨by rw [h1, hlen'], h2⟩
    · simp only [WP.dspec_ok]
      exact ⟨trivial, hvalid⟩

theorem cache.ProgramCache.grow_loop1_spec (v : alloc.vec.Vec cache.ProgramEntry) (size : Std.Usize)
    (hmax : v.length ≤ U32.max) (slots : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (hlen : slots.length = size.val ∧ 0 < size.val) (hi : i.val ≤ v.length) (hvalid : SlotsValid slots.val v.length) :
    cache.ProgramCache.grow_loop1 v size slots i ⦃ slots' =>
      slots'.length = slots.length ∧ SlotsValid slots'.val v.length ⦄div := by
  revert slots i
  apply cache.ProgramCache.grow_loop1.fixpoint_induct v size
    (motive := fun f => ∀ (slots : alloc.vec.Vec Std.U32) (i : Std.Usize),
      slots.length = size.val ∧ 0 < size.val → i.val ≤ v.length → SlotsValid slots.val v.length →
      f slots i ⦃ slots' =>
        slots'.length = slots.length ∧ SlotsValid slots'.val v.length ⦄div)
  · prove_adm
  · intro loop ih slots i hlen hi hvalid
    simp only
    split
    · rename_i hlt
      step as ⟨entry, hentry⟩
      step as ⟨i2⟩
      step as ⟨i3, hi3⟩
      step as ⟨m, hm⟩
      step as ⟨slot, hslot⟩
      have hslotlt : slot.val < slots.length := by
        have : slot.val ≤ m.val := by rw [hslot]; simp; exact Nat.and_le_right
        scalar_tac
      step with cache.ProgramCache.grow_loop1_loop0_spec size slots (by scalar_tac) slot hslotlt as ⟨slot1, hslot1⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨old, back, hold, hback⟩
      step as ⟨i7, hi7⟩
      have hset : (back i6).val = slots.val.set slot1.val i6 := by simp [hback]
      have hlen' : (back i6).length = slots.length := by
        simp [alloc.vec.Vec.length, hset]
      have hi6v : i6.val ≤ v.length := by scalar_tac
      apply WP.dspec_mono (ih (back i6) i7 (by rw [hlen']; exact hlen) (by scalar_tac)
        (by rw [hset]; exact hvalid.set _ hi6v))
      intro slots' ⟨h1, h2⟩
      exact ⟨by rw [h1, hlen'], h2⟩
    · simp only [WP.dspec_ok]
      exact ⟨trivial, hvalid⟩

theorem cache.ProgramCache.insert_loop0_spec (args : Slice Term) (key : alloc.vec.Vec Term)
    (i : Std.Usize) (hi : i.val ≤ args.length) (hkey : key.val = args.val.take i.val) :
    cache.ProgramCache.insert_loop0 args key i ⦃ key' => key'.val = args.val ⦄div := by
  revert key i
  apply cache.ProgramCache.insert_loop0.fixpoint_induct args
    (motive := fun f => ∀ (key : alloc.vec.Vec Term) (i : Std.Usize),
      i.val ≤ args.length → key.val = args.val.take i.val →
      f key i ⦃ key' => key'.val = args.val ⦄div)
  · prove_adm
  · intro loop ih key i hi hkey
    simp only
    split
    · rename_i hlt
      have hilt : i.val < args.val.length := by scalar_tac
      step as ⟨t, ht⟩
      have hklen : key.length = i.val := by
        simp [alloc.vec.Vec.length, hkey]; omega
      step as ⟨key1, hkey1⟩
      step as ⟨i2, hi2⟩
      apply ih key1 i2 (by scalar_tac)
      rw [hkey1, hkey, hi2, ht, List.take_succ_eq_append_getElem hilt]
    · rename_i hge
      simp only [WP.dspec_ok]
      rw [hkey]
      apply List.take_of_length_le
      have : args.val.length = args.length := rfl
      scalar_tac

theorem cache.ProgramCache.insert_loop1_spec (args : Slice Term) (key : alloc.vec.Vec Term)
    (i : Std.Usize) (hi : i.val ≤ args.length) (hkey : key.val = args.val.take i.val) :
    cache.ProgramCache.insert_loop1 args key i ⦃ key' => key'.val = args.val ⦄div := by
  revert key i
  apply cache.ProgramCache.insert_loop1.fixpoint_induct args
    (motive := fun f => ∀ (key : alloc.vec.Vec Term) (i : Std.Usize),
      i.val ≤ args.length → key.val = args.val.take i.val →
      f key i ⦃ key' => key'.val = args.val ⦄div)
  · prove_adm
  · intro loop ih key i hi hkey
    simp only
    split
    · rename_i hlt
      have hilt : i.val < args.val.length := by scalar_tac
      step as ⟨t, ht⟩
      have hklen : key.length = i.val := by
        simp [alloc.vec.Vec.length, hkey]; omega
      step as ⟨key1, hkey1⟩
      step as ⟨i2, hi2⟩
      apply ih key1 i2 (by scalar_tac)
      rw [hkey1, hkey, hi2, ht, List.take_succ_eq_append_getElem hilt]
    · rename_i hge
      simp only [WP.dspec_ok]
      rw [hkey]
      apply List.take_of_length_le
      have : args.val.length = args.length := rfl
      scalar_tac

/-- `grow` keeps the entries and the table well formed; when it answers
`true` the table has slots. -/
theorem cache.ProgramCache.grow_spec (pc : cache.ProgramCache) (hwf : CacheWf pc) :
    cache.ProgramCache.grow pc ⦃ b pc' =>
      CacheWf pc' ∧ pc'.entries = pc.entries ∧ pc'.max_entries = pc.max_entries ∧
      (b = true → 0 < pc'.slots.length) ∧ (b = false → pc' = pc) ⦄div := by
  unfold cache.ProgramCache.grow
  step as ⟨b, hb⟩
  split
  · step as ⟨slots, hslots, hslen⟩
    step with cache.ProgramCache.grow_loop0_spec pc.entries hwf.hmax slots 0#usize
      (by simpa using hslen) (by simp) (by rw [hslots]; exact SlotsValid.replicate _ _)
      as ⟨slots1, hl1, hv1⟩
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    refine ⟨⟨hv1, hwf.hmax⟩, trivial, trivial, ?_, by simp⟩
    intro _
    show 0 < slots1.length
    rw [hl1]; simp [hslen]
  · rename_i hne
    have hpos : 0 < pc.slots.length := by
      simp [hb] at hne; exact List.length_pos_of_ne_nil hne
    step as ⟨o, ho⟩
    cases o with
    | none => simp; exact hwf
    | some size =>
      simp only at ho ⊢
      obtain ⟨_, hsize, _⟩ := ho
      step as ⟨slots, hslots, hslen⟩
      have hsz : 0 < size.val := by
        have : pc.slots.len.val = pc.slots.length := by scalar_tac
        rw [hsize, this]; omega
      step with cache.ProgramCache.grow_loop1_spec pc.entries size hwf.hmax slots 0#usize
        ⟨by simpa using hslen, hsz⟩ (by simp) (by rw [hslots]; exact SlotsValid.replicate _ _)
        as ⟨slots1, hl1, hv1⟩
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨⟨hv1, hwf.hmax⟩, trivial, trivial, ?_, by simp⟩
      intro _
      show 0 < slots1.length
      rw [hl1, hslen]; exact hsz

/-- What `insert` may do to a cache: nothing to its entries, or one more
entry, for the program, arguments and result given. -/
def CacheAdds (pc pc' : cache.ProgramCache) (program : cache.ProgramId) (args : Slice Term)
    (result : Term) : Prop :=
  CacheWf pc' ∧ pc'.max_entries = pc.max_entries ∧
  (pc'.entries = pc.entries ∨
    ∃ key : alloc.vec.Vec Term, key.val = args.val ∧
      pc'.entries.val = pc.entries.val ++ [{ program, args := key, result }])

/-- The end of `insert`, in either of its two branches. -/
theorem cache.ProgramCache.insert_tail (pc : cache.ProgramCache) (hwf : CacheWf pc)
    (hpos : 0 < pc.slots.length) (hlt : pc.entries.length < U32.max)
    (program : cache.ProgramId) (args : Slice Term) (result : Term)
    (loopf : Slice Term → alloc.vec.Vec Term → Std.Usize → Result (alloc.vec.Vec Term))
    (hloop : loopf args (alloc.vec.Vec.new Term) 0#usize ⦃ key' => key'.val = args.val ⦄div) :
    (do
      let slot ← cache.ProgramCache.find pc program args
      let i6 ← pc.slots.index_usize slot
      if (i6 != 0#u32) = true
      then ok pc
      else do
        let key ← loopf args (alloc.vec.Vec.new Term) 0#usize
        let v ← pc.entries.push ({ program, args := key, result } : cache.ProgramEntry)
        let (_, index_mut_back) ← pc.slots.index_mut_usize slot
        let i8 ← lift (UScalar.cast .U32 v.len)
        ok ({ entries := v, slots := index_mut_back i8, max_entries := pc.max_entries } :
          cache.ProgramCache)) ⦃ pc' =>
      CacheAdds pc pc' program args result ⦄div := by
  step with cache.ProgramCache.find_spec pc hwf hpos as ⟨slot, hhit⟩
  obtain ⟨hslot, _⟩ := hhit
  step as ⟨i6, hi6⟩
  split
  · simp only [WP.dspec_ok]
    exact ⟨hwf, rfl, Or.inl rfl⟩
  · step with hloop as ⟨key, hkey⟩
    step as ⟨v, hv⟩
    step as ⟨old, back, hold, hback⟩
    step as ⟨i8, hi8⟩
    simp only [WP.dspec_ok]
    have hvlen : v.length = pc.entries.length + 1 := by simp [alloc.vec.Vec.length, hv]
    have hi8v : i8.val = pc.entries.length + 1 := by
      rw [hi8]; scalar_tac
    refine ⟨⟨?_, ?_⟩, rfl, Or.inr ⟨key, hkey, hv⟩⟩
    · show SlotsValid (back i8).val v.length
      have hset : (back i8).val = pc.slots.val.set slot.val i8 := by simp [hback]
      rw [hset, hvlen]
      exact (SlotsValid.mono hwf.valid (Nat.le_succ _)).set _ (by omega)
    · show v.length ≤ U32.max
      rw [hvlen]; omega

/-- `insert` keeps the table well formed and adds at most the entry for
what it is given. -/
theorem cache.ProgramCache.insert_spec (pc : cache.ProgramCache) (hwf : CacheWf pc)
    (program : cache.ProgramId) (args : Slice Term) (result : Term) :
    cache.ProgramCache.insert pc program args result ⦃ pc' =>
      CacheAdds pc pc' program args result ⦄div := by
  unfold cache.ProgramCache.insert
  dsimp only
  split
  · simp only [WP.dspec_ok]; exact ⟨hwf, rfl, Or.inl rfl⟩
  · step as ⟨i2, hi2⟩
    split
    · simp only [WP.dspec_ok]; exact ⟨hwf, rfl, Or.inl rfl⟩
    · rename_i hnmax
      have hlt : pc.entries.length < U32.max := by
        have : i2.val = U32.max := by
          rw [hi2]; simp [core.num.U32.MAX, U32.rMax, U32.max, U32.numBits]
        scalar_tac
      step as ⟨i5, hi5⟩
      split
      · step with cache.ProgramCache.grow_spec pc hwf as ⟨b, pc1, hwf1, he1, hm1, hb1, hb0⟩
        split
        · rename_i hbt
          have hpos := hb1 hbt
          have hlt1 : pc1.entries.length < U32.max := by rw [he1]; exact hlt
          apply WP.dspec_mono (cache.ProgramCache.insert_tail pc1 hwf1 hpos hlt1 program args
            result cache.ProgramCache.insert_loop0
            (cache.ProgramCache.insert_loop0_spec args _ 0#usize (by simp) (by simp)))
          rintro pc' ⟨h1, h2, h3⟩
          refine ⟨h1, by rw [h2, hm1], ?_⟩
          rw [he1] at h3; exact h3
        · rename_i hbf
          simp only [WP.dspec_ok]
          have : pc1 = pc := hb0 (by simpa using hbf)
          rw [this]; exact ⟨hwf, rfl, Or.inl rfl⟩
      · rename_i hsmall
        have hpos : 0 < pc.slots.length := by scalar_tac
        exact cache.ProgramCache.insert_tail pc hwf hpos hlt program args result
          cache.ProgramCache.insert_loop1
          (cache.ProgramCache.insert_loop1_spec args _ 0#usize (by simp) (by simp))

end pathos_compiled_checker
