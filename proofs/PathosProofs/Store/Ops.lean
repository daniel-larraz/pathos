module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Store.Intern

/-!
# The store's operations on terms

What `view`, `is_stuck`, `unapply`, `apply`, `construct` and `destruct` do,
in terms of the data of the terms.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `view` is the data of a handle of the store, and an error for any other. -/
theorem Store.view_eq (s : Store) (t : Term) :
    Store.view s t = ok (if t.val < s.nodes.length then
        core.result.Result.Ok (s.nodes.val[t.val]!)
      else core.result.Result.Err CheckError.InvalidHandle) := by
  unfold Store.view
  simp [lift, core.slice.Slice.get, core.option.Option.ok_or]
  have hd : (s.nodes.deref).val = s.nodes.val := by simp [alloc.vec.Vec.deref]
  rw [hd]
  by_cases h : t.val < s.nodes.val.length <;> simp [h]

/-- The data of a handle. -/
def Store.data (s : Store) (t : Term) : TermData := s.nodes.val[t.val]!

theorem Store.stuck_eq (s : Store) : Store.stuck s = ok 0#u32 := rfl

/-- Whether data is that of the stuck term. -/
def TermData.isStuck : TermData → Bool
  | TermData.Stuck => true
  | _ => false

theorem TermData.isStuck_iff (d : TermData) : d.isStuck = true ↔ d = TermData.Stuck := by
  cases d <;> simp [TermData.isStuck]

theorem Store.is_stuck_eq (s : Store) (t : Term) :
    Store.is_stuck s t = ok (if t.val < s.nodes.length then
        core.result.Result.Ok (s.data t).isStuck
      else core.result.Result.Err CheckError.InvalidHandle) := by
  unfold Store.is_stuck
  rw [Store.view_eq]
  by_cases h : t.val < s.nodes.length
  · simp only [h, ite_true, core.result.Result.Insts.CoreOpsTry.branch, Store.data]
    cases hd : s.nodes.val[t.val]! <;> simp [TermData.isStuck]
  · simp [h, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem Store.unapply_eq (s : Store) (t : Term) :
    Store.unapply s t = ok (if t.val < s.nodes.length then
        core.result.Result.Ok (match s.data t with
          | TermData.Apply f a => some (f, a)
          | _ => none)
      else core.result.Result.Err CheckError.InvalidHandle) := by
  unfold Store.unapply
  rw [Store.view_eq]
  by_cases h : t.val < s.nodes.length
  · simp only [h, ite_true, core.result.Result.Insts.CoreOpsTry.branch, Store.data]
    cases hd : s.nodes.val[t.val]! <;> simp
  · simp [h, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Data whose handles are handles of `nodes`, an application being of two
terms that are not stuck, a node having as many fields as its constructor
takes. -/
def TermData.Wf (nodes : List TermData) : TermData → Prop
  | TermData.Apply f a =>
    f.val < nodes.length ∧ a.val < nodes.length ∧
    nodes[f.val]! ≠ TermData.Stuck ∧ nodes[a.val]! ≠ TermData.Stuck
  | TermData.Node c fields =>
    (∀ x ∈ fields.val, x.val < nodes.length) ∧
    ∃ n : Std.Usize, c.arity = ok n ∧ n.val = fields.length
  | _ => True

theorem TermData.Wf.mono {nodes nodes' : List TermData} {d : TermData}
    (hpre : nodes <+: nodes') (h : d.Wf nodes) : d.Wf nodes' := by
  have hlen := hpre.length_le
  have hget : ∀ i : Nat, i < nodes.length → nodes'[i]! = nodes[i]! := by
    intro i hi
    obtain ⟨r, rfl⟩ := hpre
    simp [List.getElem?_append_left hi]
  cases d <;> simp only [TermData.Wf] at h ⊢
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by omega, by omega, by rw [hget _ h1]; exact h3, by rw [hget _ h2]; exact h4⟩
  · exact ⟨fun x hx => by have := h.1 x hx; omega, h.2⟩

/-- The terms of a store are well formed: the first is the stuck term, and
a term's data refers to earlier terms only. -/
structure Store.Wf (s : Store) : Prop where
  nonempty : 0 < s.nodes.length
  stuck0 : s.nodes.val[0]! = TermData.Stuck
  wf : ∀ t : Nat, t < s.nodes.length → (s.nodes.val[t]!).Wf (s.nodes.val.take t)

/-- The invariant of the store. -/
structure Store.Inv (s : Store) : Prop where
  table : StoreInv s
  terms : s.Wf

theorem Store.Wf.data {s : Store} (h : s.Wf) (t : Nat) (ht : t < s.nodes.length) :
    (s.nodes.val[t]!).Wf s.nodes.val :=
  (h.wf t ht).mono (List.take_prefix _ _)

/-- `intern` of well-formed data keeps the store's invariant. -/
theorem Store.intern_inv (s : Store) (data : TermData) (hinv : s.Inv)
    (hd : data.Wf s.nodes.val) (h64 : 2 ^ 40 ≤ Usize.max) :
    Store.intern s data ⦃ r s' =>
      s'.Inv ∧ s.Extends s' ∧
      match r with
      | core.result.Result.Ok t => t.val < s'.nodes.length ∧ s'.data t = data
      | core.result.Result.Err _ => s' = s ⦄div := by
  apply WP.dspec_mono (Store.intern_spec s data hinv.table h64)
  rintro ⟨r, s'⟩ ⟨htable, hext, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  cases r with
  | Err e => simp only at hr; subst hr; exact ⟨hinv, hext, rfl⟩
  | Ok t =>
    simp only at hr ⊢
    obtain ⟨hlt, hdata, hshape⟩ := hr
    refine ⟨⟨htable, ?_⟩, hext, hlt, hdata⟩
    rcases hshape with hsame | happ
    · constructor
      · simp only [alloc.vec.Vec.length, hsame]; exact hinv.terms.nonempty
      · rw [hsame]; exact hinv.terms.stuck0
      · intro u hu
        simp only [alloc.vec.Vec.length, hsame] at hu ⊢
        exact hinv.terms.wf u hu
    · have hn := hinv.terms.nonempty
      constructor
      · simp [alloc.vec.Vec.length, happ]
      · rw [happ]
        have hn' : 0 < s.nodes.val.length := hn
        rw [getElem!_append_left _ _ _ hn']; exact hinv.terms.stuck0
      · intro u hu
        simp only [alloc.vec.Vec.length, happ, List.length_append, List.length_singleton] at hu
        rw [happ]
        by_cases hun : u = s.nodes.val.length
        · subst hun
          simpa using hd
        · have hu' : u < s.nodes.val.length := by omega
          have h1 : (s.nodes.val ++ [data])[u]! = s.nodes.val[u]! :=
            getElem!_append_left _ _ _ hu'
          have h2 : (s.nodes.val ++ [data]).take u = s.nodes.val.take u := by
            rw [List.take_append_of_le_length (by omega)]
          rw [h1, h2]
          exact hinv.terms.wf u hu'

/-- `apply` gives the application of two terms as a term, or the stuck
term when one of them is stuck. -/
theorem Store.apply_spec (s : Store) (f a : Term) (hinv : s.Inv) (h64 : 2 ^ 40 ≤ Usize.max) :
    Store.apply s f a ⦃ r s' =>
      s'.Inv ∧ s.Extends s' ∧
      match r with
      | core.result.Result.Ok t =>
        f.val < s.nodes.length ∧ t.val < s'.nodes.length ∧
        if (s.data f).isStuck then t = 0#u32 ∧ s' = s
        else a.val < s.nodes.length ∧
          if (s.data a).isStuck then t = 0#u32 ∧ s' = s
          else s'.data t = TermData.Apply f a
      | core.result.Result.Err _ => s' = s ⦄div := by
  unfold Store.apply
  rw [Store.is_stuck_eq]
  have hne := hinv.terms.nonempty
  by_cases hf : f.val < s.nodes.length
  · by_cases hfs : (s.data f).isStuck = true
    · simp [hf, hfs, Store.stuck_eq, core.result.Result.Insts.CoreOpsTry.branch]
      exact ⟨hinv, Store.Extends.refl s, hne⟩
    · rw [Store.is_stuck_eq]
      by_cases ha : a.val < s.nodes.length
      · by_cases has : (s.data a).isStuck = true
        · simp [hf, hfs, ha, has, Store.stuck_eq, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hinv, Store.Extends.refl s, hne⟩
        · simp [hf, hfs, ha, has, Store.stuck_eq, core.result.Result.Insts.CoreOpsTry.branch]
          refine Store.intern_inv s (TermData.Apply f a) hinv ?_ h64
          refine ⟨hf, ha, ?_, ?_⟩
          · intro h; exact hfs ((TermData.isStuck_iff _).mpr h)
          · intro h; exact has ((TermData.isStuck_iff _).mpr h)
      · simp [hf, hfs, ha, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact ⟨hinv, Store.Extends.refl s⟩
  · simp [hf, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv, Store.Extends.refl s⟩

end pathos_compiled_checker
