module
public import CpcChecker
public import PathosProofs.Store.Table

/-!
# `TermCounts`: how many times each term of a list occurs (CPC only)

The runtime's `table::TermCounts`, which `eo::list_setof`, `eo::list_diff`,
`eo::list_inter`, `eo::list_meq` and `eo::list_minclude` use: an
open-addressed table of entries (a slot is 0 or an entry's place plus one),
searched from the slot a term's hash names through the slots that are
taken, as the store's table (PathosProofs/Store/Table.lean, whose `Path` this
reuses). The specs are of partial correctness, as the loops' are: a search
that did not end would satisfy them.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-! ## The hash of a term -/

theorem table_mix_ok (h w : Std.U64) : table.mix h w ⦃ _ => True ⦄ := by
  unfold table.mix; step*

theorem table_fold_ok (h : Std.U64) : table.fold h ⦃ _ => True ⦄ := by
  unfold table.fold; step*

/-- The hash a term's search starts from: what `fold (mix 0 t)` gives. -/
noncomputable def tcHash (t : Term) : Nat :=
  Classical.epsilon (fun n : Nat => ∃ m h,
    table.mix 0#u64 (core.convert.num.FromU64U32.from t) = ok m ∧
    table.fold m = ok h ∧ n = h.val)

theorem tcHash_eq {t : Term} {m : Std.U64} {h : Std.U32}
    (hm : table.mix 0#u64 (core.convert.num.FromU64U32.from t) = ok m)
    (hh : table.fold m = ok h) : tcHash t = h.val := by
  have hex : ∃ n : Nat, ∃ m h,
      table.mix 0#u64 (core.convert.num.FromU64U32.from t) = ok m ∧
      table.fold m = ok h ∧ n = h.val := ⟨h.val, m, h, hm, hh, rfl⟩
  obtain ⟨m', h', hm', hh', he⟩ := Classical.epsilon_spec hex
  unfold tcHash; rw [he]
  have e1 : m' = m := by have := hm'.symm.trans hm; simpa using this
  subst e1
  have e2 : h' = h := by have := hh'.symm.trans hh; simpa using this
  rw [e2]

/-! ## The table -/

/-- The table holds the terms `keys`, each once, with their counts: each
key's search reaches its slot through taken slots, and each taken slot
holds one of the keys. -/
structure TC (tc : table.TermCounts) (keys : List Term) (counts : List Nat) : Prop where
  keys_eq : tc.keys.val = keys
  counts_eq : tc.counts.val.map (·.val) = counts
  counts_len : counts.length = keys.length
  nodup : keys.Nodup
  slots_pos : 0 < tc.slots.length
  reach : ∀ k : Nat, k < keys.length → ∃ z, z < tc.slots.length ∧
    (tc.slots.val[z]! : Std.U32).val = k + 1 ∧
    Path tc.slots.val (tc.slots.length - 1) (tcHash keys[k]! &&& (tc.slots.length - 1)) z
  valid : ∀ z : Nat, tc.slots.val[z]! ≠ 0#u32 → (tc.slots.val[z]! : Std.U32).val ≤ keys.length

/-- A path continues past a taken slot. -/
theorem Path.snoc {slots : List Std.U32} {mask i j : Nat} (h : Path slots mask i j)
    (hj : slots[j]! ≠ 0#u32) : Path slots mask i ((j + 1) &&& mask) := by
  induction h with
  | here i => exact Path.step i _ hj (Path.here _)
  | step i j hi _ ih => exact Path.step i _ hi (ih hj)

/-- While `slot` searches from slot `i`: the entry of `t`, if `t` is a key,
is still ahead. -/
def TCAhead (slots : List Std.U32) (keys : List Term) (t : Term) (mask i : Nat) : Prop :=
  ∀ k : Nat, k < keys.length → keys[k]! = t →
    ∃ z, (slots[z]! : Std.U32).val = k + 1 ∧ Path slots mask i z

/-- What `slot` answers: a slot in range that holds `t`'s entry, or is free
and `t` is no key. -/
def TCSlot (slots : List Std.U32) (keys : List Term) (t : Term) (i : Nat) : Prop :=
  i < slots.length ∧
  (slots[i]! = 0#u32 → t ∉ keys) ∧
  (slots[i]! ≠ 0#u32 → ∃ k, (slots[i]! : Std.U32).val = k + 1 ∧ k < keys.length ∧ keys[k]! = t)

theorem slot_loop_spec (v : alloc.vec.Vec Std.U32) (v1 : alloc.vec.Vec Term) (t : Term)
    (mask : Std.Usize) (hmask : mask.val < v.length)
    (hvalid : ∀ z : Nat, v.val[z]! ≠ 0#u32 → (v.val[z]! : Std.U32).val ≤ v1.length)
    (start : Nat) (i : Std.Usize) (searching : Bool) (hi : i.val < v.length)
    (hp : Path v.val mask.val start i.val)
    (h : if searching then TCAhead v.val v1.val t mask.val i.val else TCSlot v.val v1.val t i.val) :
    table.TermCounts.slot_loop v v1 t mask i searching ⦃ r =>
      TCSlot v.val v1.val t r.val ∧ Path v.val mask.val start r.val ⦄div := by
  revert i searching
  apply table.TermCounts.slot_loop.fixpoint_induct v v1 t mask
    (motive := fun f => ∀ (i : Std.Usize) (searching : Bool), i.val < v.length →
      Path v.val mask.val start i.val →
      (if searching then TCAhead v.val v1.val t mask.val i.val else TCSlot v.val v1.val t i.val) →
      f i searching ⦃ r => TCSlot v.val v1.val t r.val ∧ Path v.val mask.val start r.val ⦄div)
  · prove_adm
  · intro loop ih i searching hi hp h
    simp only
    split
    · rename_i hs
      simp only [hs, ite_true] at h
      step as ⟨s, hs'⟩
      have hsi : v.val[i.val]! = s := by simp [hs', hi]
      split
      · rename_i hzero
        apply ih i false hi hp
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨hi, ?_, ?_⟩
        · intro _ hmem
          obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.mp hmem
          obtain ⟨z, hz, hpath⟩ := h k hk (by rw [getElem!_pos v1.val k hk]; exact hkt)
          cases hpath with
          | here => rw [hsi, hzero] at hz; simp at hz
          | step _ _ hne _ => rw [hsi, hzero] at hne; simp at hne
        · intro hne; rw [hsi, hzero] at hne; simp at hne
      · rename_i hnz
        have hsv : s.val ≤ v1.length := by
          have := hvalid i.val (by rw [hsi]; exact hnz)
          rw [hsi] at this; exact this
        have hspos : 0 < s.val := by scalar_tac
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        have hi3v : i3.val = s.val - 1 := by scalar_tac
        have hi3lt : i3.val < v1.val.length := by scalar_tac
        step as ⟨t', ht'⟩
        have ht'k : v1.val[s.val - 1]! = t' := by
          rw [← hi3v, getElem!_pos v1.val i3.val hi3lt]; exact ht'.symm
        simp only [Term.Insts.CoreCmpPartialEqTerm.eq, Std.bind_ok]
        split
        · rename_i hb
          have htt : t' = t := by simpa using hb
          apply ih i false hi hp
          simp only [Bool.false_eq_true, ite_false]
          refine ⟨hi, fun hz => absurd (hsi.symm.trans hz) hnz, fun _ => ⟨s.val - 1, ?_, by omega, ?_⟩⟩
          · rw [hsi]; omega
          · rw [ht'k, htt]
        · rename_i hb
          have htt : ¬ t' = t := by simpa using hb
          step as ⟨i4, hi4⟩
          step as ⟨i5, hi5⟩
          have h5 : i5.val = (i.val + 1) &&& mask.val := by rw [hi5]; simp [hi4]
          have h5lt : i5.val < v.length := by
            have : i5.val ≤ mask.val := by rw [h5]; exact Nat.and_le_right
            omega
          apply ih i5 searching h5lt (h5 ▸ hp.snoc (by rw [hsi]; exact hnz))
          simp only [hs, ite_true]
          intro k hk hkt
          obtain ⟨z, hz, hpath⟩ := h k hk hkt
          cases hpath with
          | here =>
            rw [hsi] at hz
            have : k = s.val - 1 := by omega
            subst this
            exact absurd (ht'k.symm.trans hkt) htt
          | step _ _ _ hrest => exact ⟨z, hz, h5 ▸ hrest⟩
    · rename_i hs
      simp only [hs] at h
      simp only [WP.dspec_ok]
      exact ⟨by simpa using h, hp⟩

/-- `slot`: where `t`'s search ends. -/
theorem slot_spec (tc : table.TermCounts) {keys : List Term} {counts : List Nat}
    (hTC : TC tc keys counts) (t : Term) :
    table.TermCounts.slot tc t ⦃ i => TCSlot tc.slots.val keys t i.val ∧
      Path tc.slots.val (tc.slots.length - 1) (tcHash t &&& (tc.slots.length - 1)) i.val ⦄div := by
  obtain ⟨m, hm, -⟩ := spec_returns (table_mix_ok 0#u64 (core.convert.num.FromU64U32.from t))
  obtain ⟨h, hh, -⟩ := spec_returns (table_fold_ok m)
  have hhash := tcHash_eq hm hh
  have hpos := hTC.slots_pos
  unfold table.TermCounts.slot
  step as ⟨mask, hmask⟩
  simp only [lift, Std.bind_ok, hm, hh]
  have hmask' : mask.val = tc.slots.length - 1 := by scalar_tac
  have hstart : ((UScalar.cast UScalarTy.Usize h) &&& mask).val = tcHash t &&& (tc.slots.length - 1) := by
    simp [hhash, hmask']
  have hlt : ((UScalar.cast UScalarTy.Usize h) &&& mask).val < tc.slots.length := by
    have : ((UScalar.cast UScalarTy.Usize h) &&& mask).val ≤ mask.val := by simp; exact Nat.and_le_right
    omega
  have hv1 : ∀ z : Nat, tc.slots.val[z]! ≠ 0#u32 → (tc.slots.val[z]! : Std.U32).val ≤ tc.keys.length := by
    intro z hz; have := hTC.valid z hz; simp only [alloc.vec.Vec.length, hTC.keys_eq]; exact this
  apply WP.dspec_mono (slot_loop_spec tc.slots tc.keys t mask (by omega) hv1
    (tcHash t &&& (tc.slots.length - 1)) _ true hlt (by rw [hstart, ← hmask']; exact Path.here _) ?_)
  · intro r hr; rw [hTC.keys_eq, hmask'] at hr; exact hr
  simp only [ite_true]
  intro k hk hkt
  rw [hTC.keys_eq] at hk hkt
  obtain ⟨z, -, hz, hpath⟩ := hTC.reach k hk
  refine ⟨z, hz, ?_⟩
  rw [hstart, hmask', ← hkt]; exact hpath

/-- `entry`: the place of `t`'s entry, if it has one. -/
theorem entry_spec (tc : table.TermCounts) {keys : List Term} {counts : List Nat}
    (hTC : TC tc keys counts) (t : Term) :
    table.TermCounts.entry tc t ⦃ o =>
      match o with
      | none => t ∉ keys
      | some p => p.val < keys.length ∧ keys[p.val]! = t ⦄div := by
  unfold table.TermCounts.entry
  step with slot_spec tc hTC t as ⟨i, hTS, _⟩
  obtain ⟨hlt, hzero, hnz⟩ := hTS
  step as ⟨s, hs⟩
  have hlt' : i.val < tc.slots.val.length := hlt
  have hsi : tc.slots.val[i.val]! = s := by rw [getElem!_eq _ _ hlt']; exact hs.symm
  split
  · rename_i h0
    simp only [WP.dspec_ok]
    exact hzero (hsi.trans h0)
  · rename_i h0
    obtain ⟨k, hk, hkl, hkt⟩ := hnz (by rw [hsi]; exact h0)
    rw [hsi] at hk
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    simp only [WP.dspec_ok]
    have : i2.val = k := by scalar_tac
    rw [this]; exact ⟨hkl, hkt⟩

/-- `add`: one more occurrence of `t`, as a new key with count 1, or one
more on its entry. -/
theorem add_spec (tc : table.TermCounts) {keys : List Term} {counts : List Nat}
    (hTC : TC tc keys counts) (t : Term) (hcap : keys.length + 1 < 2 ^ 32)
    (hcnt : ∀ c ∈ counts, c + 1 ≤ Usize.max) (h64 : Platform64) :
    table.TermCounts.add tc t ⦃ tc' => tc'.slots.length = tc.slots.length ∧
      (t ∉ keys → TC tc' (keys ++ [t]) (counts ++ [1])) ∧
      (∀ k, k < keys.length → keys[k]! = t →
        TC tc' keys (counts.set k (counts[k]! + 1))) ⦄div := by
  have hkl : tc.keys.val.length = keys.length := by rw [hTC.keys_eq]
  have hcl : tc.counts.val.length = counts.length := by rw [← hTC.counts_eq, List.length_map]
  unfold table.TermCounts.add
  step with slot_spec tc hTC t as ⟨i, hTS, hpath⟩
  obtain ⟨hlt, hzero, hnz⟩ := hTS
  step as ⟨s, hs⟩
  have hlt' : i.val < tc.slots.val.length := hlt
  have hsi : tc.slots.val[i.val]! = s := by rw [getElem!_eq _ _ hlt']; exact hs.symm
  split
  · rename_i h0
    have htn : t ∉ keys := hzero (hsi.trans h0)
    have hz0 : tc.slots.val[i.val]! = 0#u32 := hsi.trans h0
    have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
    have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
    have h40' : (2 : Nat) ^ 40 = 1099511627776 := by norm_num
    rw [h40'] at h40; rw [h32] at hcap
    have hkcap : tc.keys.val.length < Usize.max := by rw [hkl]; omega
    have hccap : tc.counts.val.length < Usize.max := by
      have := congrArg List.length hTC.counts_eq; simp at this; rw [hTC.counts_len] at this; omega
    step with alloc.vec.Vec.push_spec tc.keys t hkcap as ⟨v, hv⟩
    step with alloc.vec.Vec.push_spec tc.counts 1#usize hccap as ⟨v1, hv1⟩
    step as ⟨old, back, hold, hback⟩
    simp only [lift, Std.bind_ok, WP.dspec_ok]
    have hvval : v.val = keys ++ [t] := by simp [hv, hTC.keys_eq]
    have hvlen : v.val.length = keys.length + 1 := by simp [hvval]
    generalize hx : (UScalar.cast UScalarTy.U32 v.len : Std.U32) = x
    have hxv : x.val = keys.length + 1 := by
      rw [← hx]; simp only [UScalar.cast_val_eq, alloc.vec.Vec.len, hvlen]
      exact Nat.mod_eq_of_lt (by simp; omega)
    have hset : (back x).val = tc.slots.val.set i.val x := by simp [hback]
    have hslen : (back x).length = tc.slots.length := by
      simp [alloc.vec.Vec.length, hset]
    refine ⟨hslen, fun _ => ?_, fun k hk hkt =>
      absurd (List.mem_iff_getElem.mpr ⟨k, hk, by rw [← getElem!_eq _ _ hk]; exact hkt⟩) htn⟩
    constructor
    · exact hvval
    · simp [hv1, ← hTC.counts_eq]
    · simp [hTC.counts_len]
    · rw [List.nodup_append]
      refine ⟨hTC.nodup, List.nodup_singleton t, ?_⟩
      intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact htn ha
    · rw [hslen]; exact hTC.slots_pos
    · intro k hk
      rw [hslen, hset]
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hkn : k < keys.length
      · obtain ⟨z, hzl, hzv, hzp⟩ := hTC.reach k hkn
        have hzi : i.val ≠ z := by
          intro e; subst e; rw [hz0] at hzv; simp at hzv
        refine ⟨z, by simpa using hzl, ?_, ?_⟩
        · simpa [List.getElem?_set_ne hzi] using hzv
        · have : (keys ++ [t])[k]! = keys[k]! := by
            rw [getElem!_eq _ _ (by simp; omega), getElem!_eq _ _ hkn, List.getElem_append_left]
          rw [this]; simpa using hzp.set_free i.val x hz0
      · have hkk : k = keys.length := by omega
        subst hkk
        refine ⟨i.val, by simpa using hlt', ?_, ?_⟩
        · simp [hlt', hxv]
        · have : (keys ++ [t])[keys.length]! = t := by
            rw [getElem!_eq _ _ (by simp)]; simp
          rw [this]; simpa using hpath.set_free i.val x hz0
    · intro z hz
      rw [hset] at hz ⊢
      by_cases hzi : i.val = z
      · subst hzi; simp [hlt', hxv]
      · have e : (tc.slots.val.set i.val x)[z]! = tc.slots.val[z]! := by
          simp [List.getElem?_set_ne hzi]
        rw [e] at hz ⊢
        have := hTC.valid z hz
        simp only [List.length_append, List.length_singleton]
        omega
  · rename_i h0
    obtain ⟨k, hk, hkl', hkt⟩ := hnz (by rw [hsi]; exact h0)
    rw [hsi] at hk
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hi2k : i2.val = k := by scalar_tac
    have hcl' : tc.counts.val.length = counts.length := by
      have := congrArg List.length hTC.counts_eq; simpa using this
    have hkc : k < counts.length := by rw [hTC.counts_len]; exact hkl'
    step as ⟨old, back, hold, hback⟩
    have hold' : old.val = counts[k]! := by
      rw [← hTC.counts_eq, getElem!_eq _ _ (by simp; rw [hcl']; exact hkc)]
      simp [hold, hi2k]
    have hc1 : old.val + 1 ≤ Usize.max := by
      rw [hold']; exact hcnt _ (by rw [getElem!_eq _ _ hkc]; exact List.getElem_mem _)
    step as ⟨i4, hi4⟩
    simp only [WP.dspec_ok]
    refine ⟨by simp, fun hn => absurd (List.mem_iff_getElem.mpr
      ⟨k, hkl', by rw [← getElem!_eq _ _ hkl']; exact hkt⟩) hn, fun k' hk' hk't => ?_⟩
    have hkk : k' = k := by
      apply (hTC.nodup.getElem_inj_iff (hi := hk') (hj := hkl')).mp
      rw [← getElem!_eq _ _ hk', ← getElem!_eq _ _ hkl', hk't, hkt]
    subst hkk
    exact { hTC with
      counts_eq := by
        rw [hback]
        simp only [alloc.vec.Vec.set_val_eq, List.map_set, hTC.counts_eq, hi2k]
        congr 1
        rw [hi4, hold']
      counts_len := by simp [hTC.counts_len] }

/-- `slots_for`'s loop doubles from at least 16, never past `4 (n + 1)`. -/
theorem slots_for_loop_spec (n : Std.Usize) (hn : n.val ≤ 2 ^ 32) (h64 : Platform64) :
    ∀ slots : Std.Usize, 16 ≤ slots.val → slots.val ≤ max 16 (4 * (n.val + 1)) →
      table.slots_for_loop n slots ⦃ r => 0 < r.val ⦄div := by
  have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
  have h40' : (2 : Nat) ^ 40 = 1099511627776 := by norm_num
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  rw [h40'] at h40; rw [h32] at hn
  apply table.slots_for_loop.fixpoint_induct n
    (motive := fun f => ∀ slots : Std.Usize, 16 ≤ slots.val → slots.val ≤ max 16 (4 * (n.val + 1)) →
      f slots ⦃ r => 0 < r.val ⦄div)
  · prove_adm
  · intro loop ih slots h16 hmax
    simp only
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    split
    · rename_i hlt
      step as ⟨s2, hs2⟩
      apply ih s2 (by scalar_tac)
      have : slots.val / 2 < n.val + 1 := by scalar_tac
      rw [hs2]; omega
    · simp only [WP.dspec_ok]; omega

/-- `new`: an empty table. -/
theorem new_spec (n : Std.Usize) (hn : n.val ≤ 2 ^ 32) (h64 : Platform64) :
    table.TermCounts.new n ⦃ tc => TC tc [] [] ⦄div := by
  unfold table.TermCounts.new table.slots_for
  step with slots_for_loop_spec n hn h64 16#usize (by simp) (by simp) as ⟨k, hk⟩
  step with alloc.vec.from_elem_spec as ⟨v, hv, hvl⟩
  simp only [WP.dspec_ok]
  refine ⟨rfl, rfl, rfl, List.nodup_nil, ?_, fun k hk => by simp at hk, ?_⟩
  · simp [alloc.vec.Vec.length] at hvl ⊢; omega
  · intro z hz
    exfalso; apply hz
    rw [hv]
    by_cases hzl : z < k.val
    · simp [hzl]
    · simp [hzl]; rfl

/-! ## `eo::list_setof` -/

/-- One step of the runtime's walk: a term goes out unless it already has. -/
def firstOccStep {α : Type} [DecidableEq α] (acc : List α) (x : α) : List α :=
  if x ∈ acc then acc else acc ++ [x]

/-- The runtime's `first_occurrences`: the first occurrence of each term, in
order. -/
def firstOcc {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldl firstOccStep []

/-- logos's `list_setof_rec` on the elements: the first, then the rest's set
without it. -/
def setofL {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (setofL xs).filter (fun y => decide (y ≠ x))

theorem foldl_firstOccStep {α : Type} [DecidableEq α] :
    ∀ (l acc : List α),
      l.foldl firstOccStep acc = acc ++ (setofL l).filter (fun y => decide (y ∉ acc))
  | [], acc => by simp [setofL]
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_firstOccStep l]
    by_cases hx : x ∈ acc
    · simp only [firstOccStep, hx, ite_true, setofL, List.filter_cons, List.filter_filter]
      simp [hx]
      congr 1
      funext y
      by_cases hy : y ∈ acc
      · simp [hy]
      · have : y ≠ x := fun e => hy (e ▸ hx)
        simp [hy, this]
    · simp only [firstOccStep, hx, ite_false, setofL, List.filter_cons, List.filter_filter]
      simp [hx]

theorem firstOcc_eq_setofL {α : Type} [DecidableEq α] (l : List α) :
    firstOcc l = setofL l := by
  unfold firstOcc
  rw [foldl_firstOccStep]
  simp

theorem firstOcc_append {α : Type} [DecidableEq α] (l : List α) (x : α) :
    firstOcc (l ++ [x]) = firstOccStep (firstOcc l) x := by
  simp [firstOcc, List.foldl_append]

theorem firstOcc_length_le {α : Type} [DecidableEq α] (l : List α) :
    (firstOcc l).length ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [firstOcc]
  | append_singleton l x ih =>
    rw [firstOcc_append]; unfold firstOccStep; split <;> simp <;> omega

theorem firstOcc_nodup {α : Type} [DecidableEq α] (l : List α) : (firstOcc l).Nodup := by
  induction l using List.reverseRecOn with
  | nil => simp [firstOcc]
  | append_singleton l x ih =>
    rw [firstOcc_append]; unfold firstOccStep
    split
    · exact ih
    · rename_i hx
      rw [List.nodup_append]
      refine ⟨ih, List.nodup_singleton x, ?_⟩
      intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hx ha

/-- `first_occurrences`' loop: what is out is the first occurrences of the
slice's first `i` terms, and the table holds them, once each. -/
theorem first_occurrences_loop_spec (xs : Slice Term) (hxs : xs.length < 2 ^ 32)
    (h64 : Platform64) :
    ∀ (seen : table.TermCounts) (out : alloc.vec.Vec Term) (i : Std.Usize),
      i.val ≤ xs.length →
      TC seen out.val (List.replicate out.val.length 1) →
      out.val = firstOcc (xs.val.take i.val) →
      first_occurrences_loop xs seen out i ⦃ r => r.val = firstOcc xs.val ⦄div := by
  have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
  apply first_occurrences_loop.fixpoint_induct xs
    (motive := fun f => ∀ (seen : table.TermCounts) (out : alloc.vec.Vec Term) (i : Std.Usize),
      i.val ≤ xs.length →
      TC seen out.val (List.replicate out.val.length 1) →
      out.val = firstOcc (xs.val.take i.val) →
      f seen out i ⦃ r => r.val = firstOcc xs.val ⦄div)
  · prove_adm
  · intro loop ih seen out i hi hTC hout
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < xs.val.length := by simp [Slice.len, Slice.length] at hlt ⊢; scalar_tac
      have htake : xs.val.take (i.val + 1) = xs.val.take i.val ++ [xs.val[i.val]] :=
        List.take_succ_eq_append_getElem hlt'
      have hle1 : i.val + 1 ≤ xs.length := by simp only [Slice.length] at hi ⊢; omega
      have hol : out.val.length ≤ i.val := by
        rw [hout]; have := firstOcc_length_le (xs.val.take i.val); simp at this; omega
      step as ⟨t, ht⟩
      step with entry_spec seen hTC t as ⟨o, ho⟩
      cases o with
      | none =>
        simp only [Option.isNone_none, ite_true, Std.bind_ok]
        have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
        step with add_spec seen hTC t (by simp only [Slice.length] at hxs; omega)
          (by intro c hc; simp at hc; rw [hc.2]; omega) h64 as ⟨seen2, _, hnew, _⟩
        have hcap : out.val.length < Usize.max := by omega
        step with alloc.vec.Vec.push_spec out t hcap as ⟨out2, hout2⟩
        step as ⟨i2, hi2⟩
        apply ih seen2 out2 i2 (by scalar_tac)
        · rw [hout2]
          have := hnew ho
          simpa [List.replicate_succ'] using this
        · have hn : xs.val[i.val] ∉ out.val := ht ▸ ho
          rw [hout2, hi2, htake, firstOcc_append, ← hout, ← ht]
          simp [firstOccStep, ho]
      | some p =>
        obtain ⟨hp, hpt⟩ := ho
        simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Std.bind_ok]
        step as ⟨i2, hi2⟩
        apply ih seen out i2 (by scalar_tac) hTC
        rw [hi2, htake, firstOcc_append, ← hout]
        have hmem : xs.val[i.val] ∈ out.val := by
          rw [← ht, ← hpt]; exact List.mem_iff_getElem.mpr ⟨p.val, hp, (getElem!_eq _ _ hp).symm⟩
        simp [firstOccStep, hmem]
    · rename_i hge
      simp only [WP.dspec_ok]
      have : xs.val.length ≤ i.val := by simp [Slice.len, Slice.length] at hge ⊢; scalar_tac
      rw [hout, List.take_of_length_le this]

theorem first_occurrences_spec (xs : Slice Term) (hxs : xs.length < 2 ^ 32) (h64 : Platform64) :
    first_occurrences xs ⦃ r => r.val = firstOcc xs.val ⦄div := by
  unfold first_occurrences
  step with new_spec (Slice.len xs) (by scalar_tac) h64 as ⟨tc, htc⟩
  apply first_occurrences_loop_spec xs hxs h64 tc _ 0#usize (by simp) _ (by simp [firstOcc])
  simpa using htc

/-! ## The table as a multiset -/

/-- The table counts the terms of the multiset `R`: its keys, each with
the number of times `R` has it, and every term of `R` a key. -/
def TCList (tc : table.TermCounts) (R : List Term) : Prop :=
  ∃ keys counts, TC tc keys counts ∧
    (∀ k, k < keys.length → counts[k]! = R.count keys[k]!) ∧ (∀ t ∈ R, t ∈ keys)

/-- `count` at a key's place: how many times `R` has the key. -/
theorem count_spec (tc : table.TermCounts) {keys : List Term} {counts : List Nat}
    (hTC : TC tc keys counts) (p : Std.Usize) (hp : p.val < keys.length) :
    table.TermCounts.count tc p ⦃ c => c.val = counts[p.val]! ⦄div := by
  have hcl : tc.counts.val.length = keys.length := by
    have := congrArg List.length hTC.counts_eq; simp at this; rw [this, hTC.counts_len]
  unfold table.TermCounts.count
  step as ⟨c, hc⟩
  rw [← hTC.counts_eq, getElem!_eq _ _ (by simp; omega)]
  subst hc; simp

/-- `remove_one` at a key's place: one fewer of the key, if any is left. -/
theorem remove_one_spec (tc : table.TermCounts) {keys : List Term} {counts : List Nat}
    (hTC : TC tc keys counts) (p : Std.Usize) (hp : p.val < keys.length) :
    table.TermCounts.remove_one tc p ⦃ tc' =>
      tc'.slots = tc.slots ∧ TC tc' keys (counts.set p.val (counts[p.val]! - 1)) ⦄div := by
  have hcl : tc.counts.val.length = keys.length := by
    have := congrArg List.length hTC.counts_eq; simp at this; rw [this, hTC.counts_len]
  have hcp : counts[p.val]! = (tc.counts.val[p.val]'(by omega)).val := by
    rw [← hTC.counts_eq, getElem!_eq _ _ (by simp; omega)]; simp
  unfold table.TermCounts.remove_one
  step as ⟨c, hc⟩
  split
  · rename_i hpos
    step as ⟨old, back, hold, hback⟩
    step as ⟨c2, hc2⟩
    simp only [WP.dspec_ok]
    refine ⟨by simp, { hTC with counts_eq := ?_, counts_len := by simp [hTC.counts_len] }⟩
    rw [hback]
    simp only [alloc.vec.Vec.set_val_eq, List.map_set, hTC.counts_eq]
    congr 1
    rw [hc2, hold, hcp]
  · rename_i hz
    simp only [WP.dspec_ok]
    refine ⟨by simp, ?_⟩
    have hlt : p.val < counts.length := by rw [hTC.counts_len]; exact hp
    have h0 : counts[p.val]! = 0 := by rw [hcp, ← hc]; scalar_tac
    have : counts.set p.val (counts[p.val]! - 1) = counts := by
      rw [show counts[p.val]! - 1 = counts[p.val]! by rw [h0]]
      rw [getElem!_eq _ _ hlt, List.set_getElem_self]
    rw [this]; exact hTC

/-- While `multiset` adds the slice's terms: the table counts exactly the
terms added so far. -/
def MS (tc : table.TermCounts) (R : List Term) : Prop :=
  ∃ keys counts, TC tc keys counts ∧
    (∀ k, k < keys.length → counts[k]! = R.count keys[k]!) ∧
    (∀ t ∈ R, t ∈ keys) ∧ (∀ t ∈ keys, t ∈ R) ∧ keys.length ≤ R.length

theorem MS.add {tc : table.TermCounts} {R : List Term} (h : MS tc R) (t : Term)
    (hcap : R.length + 1 < 2 ^ 32) (h64 : Platform64) :
    table.TermCounts.add tc t ⦃ tc' => MS tc' (R ++ [t]) ⦄div := by
  obtain ⟨keys, counts, hTC, hcnt, hsub, hsup, hlen⟩ := h
  have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
  have hcl : counts.length = keys.length := hTC.counts_len
  have hcb : ∀ c ∈ counts, c + 1 ≤ Usize.max := by
    intro c hc
    obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.mp hc
    have := hcnt k (by omega)
    rw [getElem!_eq _ _ hk, hkc] at this
    have := List.count_le_length (a := keys[k]!) (l := R)
    have h32 : (2 : Nat) ^ 32 ≤ 2 ^ 40 := by norm_num
    omega
  apply WP.dspec_mono (add_spec tc hTC t (by omega) hcb h64)
  rintro tc' ⟨-, hnew, hold⟩
  by_cases ht : t ∈ keys
  · obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.mp ht
    have hkt' : keys[k]! = t := by rw [getElem!_eq _ _ hk]; exact hkt
    refine ⟨keys, counts.set k (counts[k]! + 1), hold k hk hkt', ?_, ?_, ?_, ?_⟩
    · intro k' hk'
      by_cases hkk : k' = k
      · subst hkk
        rw [getElem!_eq _ _ (by simp; omega), List.getElem_set_self, hcnt k' hk', hkt']
        simp
      · have hne : keys[k']! ≠ t := by
          intro e
          apply hkk
          apply (hTC.nodup.getElem_inj_iff (hi := hk') (hj := hk)).mp
          rw [← getElem!_eq _ _ hk', ← getElem!_eq _ _ hk, e, hkt']
        rw [getElem!_eq _ _ (by simp; omega), List.getElem_set_ne (Ne.symm hkk),
          ← getElem!_eq _ _ (by omega), hcnt k' hk']
        generalize keys[k']! = a at hne ⊢
        simp [List.count_append, Ne.symm hne]
    · intro x hx; simp at hx; rcases hx with hx | hx
      · exact hsub x hx
      · rw [hx]; exact ht
    · intro x hx; exact List.mem_append_left _ (hsup x hx)
    · simp; omega
  · have htR : t ∉ R := fun e => ht (hsub t e)
    refine ⟨keys ++ [t], counts ++ [1], hnew ht, ?_, ?_, ?_, ?_⟩
    · intro k' hk'
      simp only [List.length_append, List.length_singleton] at hk'
      by_cases hkl : k' < keys.length
      · have hne : keys[k']! ≠ t := by
          intro e; apply ht; rw [← e, getElem!_eq _ _ hkl]; exact List.getElem_mem _
        rw [getElem!_eq _ _ (by simp; omega), getElem!_eq _ _ (by simp; omega),
          List.getElem_append_left (by omega), List.getElem_append_left hkl,
          ← getElem!_eq _ _ (by omega), ← getElem!_eq _ _ hkl, hcnt k' hkl]
        generalize keys[k']! = a at hne ⊢
        simp [List.count_append, Ne.symm hne]
      · have hkk : k' = keys.length := by omega
        subst hkk
        rw [getElem!_eq _ _ (by simp; omega), getElem!_eq _ _ (by simp)]
        simp [List.count_append, hcl, List.count_eq_zero_of_not_mem htR]
    · intro x hx; simp at hx; rcases hx with hx | hx
      · exact List.mem_append_left _ (hsub x hx)
      · rw [hx]; simp
    · intro x hx; simp at hx; rcases hx with hx | hx
      · exact List.mem_append_left _ (hsup x hx)
      · rw [hx]; simp
    · simp; omega

theorem multiset_loop_spec (ys : Slice Term) (hys : ys.length < 2 ^ 32) (h64 : Platform64) :
    ∀ (counts : table.TermCounts) (i : Std.Usize), i.val ≤ ys.length →
      MS counts (ys.val.take i.val) →
      multiset_loop ys counts i ⦃ r => MS r ys.val ⦄div := by
  apply multiset_loop.fixpoint_induct ys
    (motive := fun f => ∀ (counts : table.TermCounts) (i : Std.Usize), i.val ≤ ys.length →
      MS counts (ys.val.take i.val) → f counts i ⦃ r => MS r ys.val ⦄div)
  · prove_adm
  · intro loop ih counts i hi hms
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < ys.val.length := by simp [Slice.len, Slice.length] at hlt ⊢; scalar_tac
      have htake : ys.val.take (i.val + 1) = ys.val.take i.val ++ [ys.val[i.val]] :=
        List.take_succ_eq_append_getElem hlt'
      step as ⟨t, ht⟩
      step with hms.add t (by simp only [Slice.length] at hys; simp; omega) h64 as ⟨c1, hc1⟩
      step as ⟨i2, hi2⟩
      apply ih c1 i2 (by simp only [Slice.length] at hi ⊢; scalar_tac)
      rw [hi2, htake, ← ht]; exact hc1
    · rename_i hge
      simp only [WP.dspec_ok]
      have : ys.val.length ≤ i.val := by simp [Slice.len, Slice.length] at hge ⊢; scalar_tac
      rw [List.take_of_length_le this] at hms; exact hms

theorem multiset_spec (ys : Slice Term) (hys : ys.length < 2 ^ 32) (h64 : Platform64) :
    multiset ys ⦃ r => MS r ys.val ⦄div := by
  unfold multiset
  step with new_spec (Slice.len ys) (by scalar_tac) h64 as ⟨tc, htc⟩
  apply multiset_loop_spec ys hys h64 tc 0#usize (by simp)
  exact ⟨[], [], htc, by simp, by simp, by simp, by simp⟩

/-- What `multiset_select` keeps of `xs` against the multiset `R`: each
term found in what is left of `R` (`paired`) or not, each find using one. -/
def selectL (paired : Bool) : List Term → List Term → List Term
  | [], _ => []
  | x :: xs, R => (if decide (x ∈ R) = paired then [x] else []) ++ selectL paired xs (R.erase x)

/-- Looking `t` up and using one: whether `R` has `t`, and the table of
`R.erase t`. -/
theorem take_one {tc : table.TermCounts} {R keys : List Term} {counts : List Nat}
    (hTC : TC tc keys counts) (hcnt : ∀ k, k < keys.length → counts[k]! = R.count keys[k]!)
    (hsub : ∀ t ∈ R, t ∈ keys) (t : Term) (o : Option Std.Usize)
    (ho : match o with
      | none => t ∉ keys
      | some p => p.val < keys.length ∧ keys[p.val]! = t) :
    (match o with
      | none => ok (tc, false)
      | some place => do
        let i2 ← table.TermCounts.count tc place
        let tc2 ← table.TermCounts.remove_one tc place
        ok (tc2, i2 > 0#usize)) ⦃ r =>
      TCList r.1 (R.erase t) ∧ r.2 = decide (t ∈ R) ⦄div := by
  cases o with
  | none =>
    simp only [WP.dspec_ok]
    have htR : t ∉ R := fun e => ho (hsub t e)
    rw [List.erase_of_not_mem htR]
    exact ⟨⟨keys, counts, hTC, hcnt, hsub⟩, by simp [htR]⟩
  | some p =>
    obtain ⟨hp, hpt⟩ := ho
    step with count_spec tc hTC p hp as ⟨c, hc⟩
    step with remove_one_spec tc hTC p hp as ⟨tc2, _, hTC2⟩
    simp only [WP.dspec_ok]
    have hct : counts[p.val]! = R.count t := by rw [hcnt p.val hp, hpt]
    refine ⟨⟨keys, _, hTC2, ?_, ?_⟩, ?_⟩
    · intro k hk
      have hkc : k < counts.length := by rw [hTC.counts_len]; exact hk
      by_cases hkp : k = p.val
      · subst hkp
        rw [getElem!_eq _ _ (by simp; omega), List.getElem_set_self, hct, hpt,
          List.count_erase_self]
      · have hne : keys[k]! ≠ t := by
          intro e; apply hkp
          apply (hTC.nodup.getElem_inj_iff (hi := hk) (hj := hp)).mp
          rw [← getElem!_eq _ _ hk, ← getElem!_eq _ _ hp, e, hpt]
        rw [getElem!_eq _ _ (by simp; omega), List.getElem_set_ne (Ne.symm hkp),
          ← getElem!_eq _ _ hkc, hcnt k hk, List.count_erase_of_ne hne]
    · intro x hx; exact hsub x (List.mem_of_mem_erase hx)
    · have : (c.val > 0) ↔ t ∈ R := by
        rw [hc, hct, gt_iff_lt, List.count_pos_iff]
      simp only [decide_eq_decide]
      constructor
      · intro h; exact this.mp (by scalar_tac)
      · intro h; have := this.mpr h; scalar_tac

theorem multiset_select_loop_spec (xs : Slice Term) (paired : Bool) (R0 : List Term)
    (h64 : Platform64) :
    ∀ (counts : table.TermCounts) (out : alloc.vec.Vec Term) (i : Std.Usize) (R : List Term),
      i.val ≤ xs.length → out.val.length ≤ i.val → TCList counts R →
      out.val ++ selectL paired (xs.val.drop i.val) R = selectL paired xs.val R0 →
      multiset_select_loop xs paired counts out i ⦃ r => r.val = selectL paired xs.val R0 ⦄div := by
  have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
  apply multiset_select_loop.fixpoint_induct xs paired
    (motive := fun f => ∀ (counts : table.TermCounts) (out : alloc.vec.Vec Term) (i : Std.Usize)
      (R : List Term), i.val ≤ xs.length → out.val.length ≤ i.val → TCList counts R →
      out.val ++ selectL paired (xs.val.drop i.val) R = selectL paired xs.val R0 →
      f counts out i ⦃ r => r.val = selectL paired xs.val R0 ⦄div)
  · prove_adm
  · intro loop ih counts out i R hi hol hTL hinv
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < xs.val.length := by simp [Slice.len, Slice.length] at hlt ⊢; scalar_tac
      have hdrop : xs.val.drop i.val = xs.val[i.val] :: xs.val.drop (i.val + 1) :=
        List.drop_eq_getElem_cons hlt'
      step as ⟨t, ht⟩
      obtain ⟨keys, cnts, hTC, hcnt, hsub⟩ := hTL
      step with entry_spec counts hTC t as ⟨o, ho⟩
      step with take_one hTC hcnt hsub t o ho as ⟨c1, found, hr1, hr2⟩
      subst hr2
      have hcap : out.val.length < Usize.max := by scalar_tac
      split
      · rename_i heq
        step with alloc.vec.Vec.push_spec out t hcap as ⟨out2, hout2⟩
        step as ⟨i2, hi2⟩
        apply ih c1 out2 i2 (R.erase t) (by scalar_tac) (by rw [hout2]; simp; omega) hr1
        rw [hout2, hi2, ← hinv, hdrop, ← ht]
        simp [selectL, heq]
      · rename_i heq
        step as ⟨i2, hi2⟩
        apply ih c1 out i2 (R.erase t) (by scalar_tac) (by omega) hr1
        rw [hi2, ← hinv, hdrop, ← ht]
        simp [selectL, heq]
    · rename_i hge
      simp only [WP.dspec_ok]
      have : xs.val.length ≤ i.val := by simp [Slice.len, Slice.length] at hge ⊢; scalar_tac
      rw [← hinv, List.drop_of_length_le this]
      simp [selectL]

theorem MS.tclist {tc : table.TermCounts} {R : List Term} (h : MS tc R) : TCList tc R := by
  obtain ⟨keys, counts, hTC, hcnt, hsub, -, -⟩ := h
  exact ⟨keys, counts, hTC, hcnt, hsub⟩

/-- `multiset_select`: the terms of `xs` that pair off with one of `ys`
(`paired`), or those that do not. -/
theorem multiset_select_spec (xs ys : Slice Term) (paired : Bool) (hys : ys.length < 2 ^ 32)
    (h64 : Platform64) :
    multiset_select xs ys paired ⦃ r => r.val = selectL paired xs.val ys.val ⦄div := by
  unfold multiset_select
  step with multiset_spec ys hys h64 as ⟨tc, htc⟩
  exact multiset_select_loop_spec xs paired ys.val h64 tc (alloc.vec.Vec.new Term) 0#usize
    ys.val (by simp) (by simp) htc.tclist (by simp)

/-! ## Multiset inclusion -/

/-- One fewer of `t` at its place: the counts of `R.erase t`. -/
theorem cnts_erase {keys R : List Term} {cnts : List Nat} (hnd : keys.Nodup)
    (hlen : cnts.length = keys.length)
    (hcnt : ∀ k, k < keys.length → cnts[k]! = R.count keys[k]!) {p : Nat} (hp : p < keys.length)
    {t : Term} (hpt : keys[p]! = t) :
    ∀ k, k < keys.length → (cnts.set p (cnts[p]! - 1))[k]! = (R.erase t).count keys[k]! := by
  intro k hk
  have hkc : k < cnts.length := by omega
  by_cases hkp : k = p
  · subst hkp
    rw [getElem!_eq _ _ (by simp; omega), List.getElem_set_self, hcnt k hk, hpt,
      List.count_erase_self]
  · have hne : keys[k]! ≠ t := by
      intro e; apply hkp
      apply (hnd.getElem_inj_iff (hi := hk) (hj := hp)).mp
      rw [← getElem!_eq _ _ hk, ← getElem!_eq _ _ hp, e, hpt]
    rw [getElem!_eq _ _ (by simp; omega), List.getElem_set_ne (Ne.symm hkp),
      ← getElem!_eq _ _ hkc, hcnt k hk, List.count_erase_of_ne hne]

/-- `ys` with each of `xs`, in turn, erased once if it has it. -/
def eraseAll (ys xs : List Term) : List Term := xs.foldl List.erase ys

theorem all_zero_loop_spec (tc : table.TermCounts) :
    ∀ (zero : Bool) (i : Std.Usize), i.val ≤ tc.counts.length →
      tc.counts.length < Usize.max →
      table.TermCounts.all_zero_loop tc zero i ⦃ b =>
        b = (zero && decide (∀ c ∈ tc.counts.val.drop i.val, c.val = 0)) ⦄div := by
  apply table.TermCounts.all_zero_loop.fixpoint_induct tc
    (motive := fun f => ∀ (zero : Bool) (i : Std.Usize), i.val ≤ tc.counts.length →
      tc.counts.length < Usize.max →
      f zero i ⦃ b => b = (zero && decide (∀ c ∈ tc.counts.val.drop i.val, c.val = 0)) ⦄div)
  · prove_adm
  · intro loop ih zero i hi hcap
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < tc.counts.val.length := by simp [alloc.vec.Vec.len] at hlt ⊢; scalar_tac
      have hdrop : tc.counts.val.drop i.val = tc.counts.val[i.val] :: tc.counts.val.drop (i.val + 1) :=
        List.drop_eq_getElem_cons hlt'
      step as ⟨c, hc⟩
      by_cases hc0 : c = 0#usize
      · simp only [hc0, bne_self_eq_false, Bool.false_eq_true, ite_false, Std.bind_ok]
        step as ⟨i3, hi3⟩
        apply WP.dspec_mono (ih zero i3 (by scalar_tac) hcap)
        intro b hb
        rw [hb, hi3, hdrop, ← hc, hc0]
        simp
      · have hne : (c != 0#usize) = true := by simpa using hc0
        simp only [hne, ite_true, Std.bind_ok]
        step as ⟨i3, hi3⟩
        apply WP.dspec_mono (ih false i3 (by scalar_tac) hcap)
        intro b hb
        rw [hb, hi3, hdrop, ← hc]
        have : c.val ≠ 0 := fun e => hc0 (UScalar.eq_of_val_eq (by simpa using e))
        simp [this]
    · rename_i hge
      simp only [WP.dspec_ok]
      have : tc.counts.val.length ≤ i.val := by simp [alloc.vec.Vec.len] at hge ⊢; scalar_tac
      simp [List.drop_of_length_le this]

theorem all_zero_spec (tc : table.TermCounts) {keys : List Term} {cnts : List Nat}
    (hTC : TC tc keys cnts) (hcap : keys.length < 2 ^ 32) (h64 : Platform64) :
    table.TermCounts.all_zero tc ⦃ b => b = decide (∀ c ∈ cnts, c = 0) ⦄div := by
  have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
  have hcl : tc.counts.length = keys.length := by
    have := congrArg List.length hTC.counts_eq; simp at this
    simp only [alloc.vec.Vec.length]; rw [this, hTC.counts_len]
  unfold table.TermCounts.all_zero
  apply WP.dspec_mono (all_zero_loop_spec tc true 0#usize (by simp) (by
    rw [hcl]; have : (2 : Nat) ^ 32 ≤ 2 ^ 40 := by norm_num
    omega))
  intro b hb
  rw [hb, ← hTC.counts_eq]
  simp

/-- While `multiset_inclusion` takes `xs`'s terms from `ys`'s counts: the
table counts what is left of `ys`, with `ys`'s terms as its keys. -/
def IncInv (tc : table.TermCounts) (ys R : List Term) : Prop :=
  ∃ keys cnts, TC tc keys cnts ∧
    (∀ k, k < keys.length → cnts[k]! = R.count keys[k]!) ∧
    (∀ t, t ∈ keys ↔ t ∈ ys) ∧ (∀ t ∈ R, t ∈ ys) ∧ keys.length < 2 ^ 32

theorem multiset_inclusion_loop_spec (xs : Slice Term) (ys : List Term) :
    ∀ (tc : table.TermCounts) (foreign : Bool) (i : Std.Usize), i.val ≤ xs.length →
      IncInv tc ys (eraseAll ys (xs.val.take i.val)) →
      foreign = decide (∃ x ∈ xs.val.take i.val, x ∉ ys) →
      multiset_inclusion_loop xs tc foreign i ⦃ r =>
        IncInv r.1 ys (eraseAll ys xs.val) ∧ r.2 = decide (∃ x ∈ xs.val, x ∉ ys) ⦄div := by
  apply multiset_inclusion_loop.fixpoint_induct xs
    (motive := fun f => ∀ (tc : table.TermCounts) (foreign : Bool) (i : Std.Usize),
      i.val ≤ xs.length → IncInv tc ys (eraseAll ys (xs.val.take i.val)) →
      foreign = decide (∃ x ∈ xs.val.take i.val, x ∉ ys) →
      f tc foreign i ⦃ r =>
        IncInv r.1 ys (eraseAll ys xs.val) ∧ r.2 = decide (∃ x ∈ xs.val, x ∉ ys) ⦄div)
  · prove_adm
  · intro loop ih tc foreign i hi hinc hfor
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < xs.val.length := by simp [Slice.len, Slice.length] at hlt ⊢; scalar_tac
      have htake : xs.val.take (i.val + 1) = xs.val.take i.val ++ [xs.val[i.val]] :=
        List.take_succ_eq_append_getElem hlt'
      have hea : eraseAll ys (xs.val.take (i.val + 1)) =
          (eraseAll ys (xs.val.take i.val)).erase xs.val[i.val] := by
        simp only [eraseAll, htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨keys, cnts, hTC, hcnt, hkey, hsub, hkl⟩ := hinc
      step as ⟨t, ht⟩
      step with entry_spec tc hTC t as ⟨o, ho⟩
      cases o with
      | none =>
        step as ⟨i2, hi2⟩
        have htys : t ∉ ys := fun e => ho ((hkey t).mpr e)
        apply ih tc true i2 (by scalar_tac)
        · rw [hi2, hea, ← ht]
          have htR : t ∉ eraseAll ys (xs.val.take i.val) := fun e => htys (hsub t e)
          rw [List.erase_of_not_mem htR]
          exact ⟨keys, cnts, hTC, hcnt, hkey, hsub, hkl⟩
        · rw [hi2, htake, ← ht]
          symm; rw [decide_eq_true_iff]; exact ⟨t, by simp, htys⟩
      | some pl =>
        obtain ⟨hp, hpt⟩ := ho
        simp only [Std.bind_ok]
        step with remove_one_spec tc hTC pl hp as ⟨tc2, _, hTC2⟩
        step as ⟨i2, hi2⟩
        apply ih tc2 foreign i2 (by scalar_tac)
        · rw [hi2, hea, ← ht]
          refine ⟨keys, _, hTC2, cnts_erase hTC.nodup hTC.counts_len hcnt hp hpt, hkey,
            fun x hx => hsub x (List.mem_of_mem_erase hx), hkl⟩
        · rw [hfor, hi2, htake, ← ht]
          have htk : t ∈ keys := by
            rw [← hpt, getElem!_eq _ _ hp]; exact List.getElem_mem _
          have htys : t ∈ ys := (hkey t).mp htk
          simp [htys]
    · rename_i hge
      simp only [WP.dspec_ok]
      have : xs.val.length ≤ i.val := by simp [Slice.len, Slice.length] at hge ⊢; scalar_tac
      rw [List.take_of_length_le this] at hinc hfor
      exact ⟨hinc, hfor⟩

/-- `multiset_inclusion`: whether some term of `xs` is no term of `ys`, and
whether taking `xs`'s terms from `ys` leaves nothing. -/
theorem multiset_inclusion_spec (xs ys : Slice Term) (hys : ys.length < 2 ^ 32)
    (h64 : Platform64) :
    multiset_inclusion xs ys ⦃ r =>
      r.1 = decide (∃ x ∈ xs.val, x ∉ ys.val) ∧ r.2 = decide (eraseAll ys.val xs.val = []) ⦄div := by
  unfold multiset_inclusion
  step with multiset_spec ys hys h64 as ⟨tc, hms⟩
  obtain ⟨keys, cnts, hTC, hcnt, hsub, hsup, hlen⟩ := hms
  step with multiset_inclusion_loop_spec xs ys.val tc false 0#usize (by simp)
    ⟨keys, cnts, hTC, by simpa [eraseAll] using hcnt, fun t => ⟨hsup t, hsub t⟩,
      fun t ht => by simpa [eraseAll] using ht, by simp only [Slice.length] at hys; omega⟩
    (by simp) as ⟨tc1, foreign, hinc, hfor⟩
  obtain ⟨keys1, cnts1, hTC1, hcnt1, hkey1, hsub1, hkl1⟩ := hinc
  step with all_zero_spec tc1 hTC1 hkl1 h64 as ⟨b, hb⟩
  simp only [WP.dspec_ok]
  refine ⟨hfor, ?_⟩
  rw [hb]
  congr 1
  apply propext
  constructor
  · intro hz
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have htk : t ∈ keys1 := (hkey1 t).mpr (hsub1 t ht)
    obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.mp htk
    have hkc : k < cnts1.length := by rw [hTC1.counts_len]; exact hk
    have := hz (cnts1[k]) (List.getElem_mem _)
    rw [← getElem!_eq _ _ hkc, hcnt1 k hk, getElem!_eq _ _ hk, hkt] at this
    exact (List.count_pos_iff.mpr ht).ne' this
  · intro hR c hc
    obtain ⟨k, hkc, hk⟩ := List.mem_iff_getElem.mp hc
    have hkk : k < keys1.length := by rw [← hTC1.counts_len]; exact hkc
    rw [← hk, ← getElem!_eq _ _ hkc, hcnt1 k hkk, hR]
    simp

/-- `eraseAll` for any type with decidable equality. -/
def eraseAllG {α : Type} [BEq α] (B A : List α) : List α := A.foldl List.erase B

/-! ## Inclusion of multisets, by counts -/

/-- logos's `list_minclude_rec` on the elements: each term of `B` in turn
taken from what is left of `A`. -/
def minclL {α : Type} [DecidableEq α] : List α → List α → Bool
  | _, [] => true
  | A, x :: B => decide (x ∈ A) && minclL (A.erase x) B

theorem minclL_iff {α : Type} [DecidableEq α] :
    ∀ (A B : List α), minclL A B = true ↔ ∀ t, B.count t ≤ A.count t
  | A, [] => by simp [minclL]
  | A, x :: B => by
    simp only [minclL, Bool.and_eq_true, decide_eq_true_eq, minclL_iff (A.erase x) B]
    constructor
    · rintro ⟨hx, h⟩ t
      have := h t
      rw [List.count_erase] at this
      by_cases htx : x = t
      · subst htx
        have h0 : 0 < A.count x := List.count_pos_iff.mpr hx
        rw [List.count_cons_self]; simp at this; omega
      · rw [List.count_cons]; simp [htx, Ne.symm htx] at this ⊢; omega
    · intro h
      have hx : x ∈ A := by
        have := h x; rw [List.count_cons_self] at this
        exact List.count_pos_iff.mp (by omega)
      refine ⟨hx, fun t => ?_⟩
      have := h t
      rw [List.count_erase, List.count_cons] at *
      by_cases htx : x = t
      · subst htx; simp at *; omega
      · simp [htx, Ne.symm htx] at *; omega

theorem count_eraseAll {α : Type} [BEq α] [LawfulBEq α] (t : α) :
    ∀ (B A : List α), (eraseAllG B A).count t = B.count t - A.count t
  | B, [] => by simp [eraseAllG]
  | B, x :: A => by
    simp only [eraseAllG, List.foldl_cons]
    rw [show A.foldl List.erase (B.erase x) = eraseAllG (B.erase x) A from rfl,
      count_eraseAll t (B.erase x) A, List.count_erase, List.count_cons]
    by_cases htx : x = t
    · subst htx; simp; omega
    · simp [htx, Ne.symm htx]

theorem eraseAll_nil_iff {α : Type} [BEq α] [LawfulBEq α] (B A : List α) :
    eraseAllG B A = [] ↔ ∀ t, B.count t ≤ A.count t := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h t
    have := h t
    rw [← List.count_pos_iff, count_eraseAll] at this
    omega
  · intro h t ht
    rw [← List.count_pos_iff, count_eraseAll] at ht
    have := h t; omega

/-- `eo::list_meq`'s test in the runtime (no foreign term, inclusion, equal
lengths) is inclusion both ways. -/
theorem meq_iff {α : Type} [DecidableEq α] (A B : List α) :
    ((¬ ∃ x ∈ A, x ∉ B) ∧ (∀ t, B.count t ≤ A.count t) ∧ A.length = B.length) ↔
      ((∀ t, B.count t ≤ A.count t) ∧ (∀ t, A.count t ≤ B.count t)) := by
  constructor
  · rintro ⟨-, hBA, hlen⟩
    have hsub : B.Subperm A := List.subperm_iff_count.mpr hBA
    have hperm : B.Perm A := hsub.perm_of_length_le (by omega)
    exact ⟨hBA, fun t => (hperm.count_eq t).ge⟩
  · rintro ⟨hBA, hAB⟩
    have hperm : B.Perm A :=
      (List.subperm_iff_count.mpr hBA).antisymm (List.subperm_iff_count.mpr hAB)
    refine ⟨?_, hBA, hperm.length_eq.symm⟩
    rintro ⟨x, hx, hxB⟩
    exact hxB (hperm.mem_iff.mpr hx)

end pathos_compiled_checker
