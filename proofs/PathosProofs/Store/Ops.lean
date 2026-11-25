module
public import MiniChecker
public import PathosProofs.Util
public import CpcMini.Logos
public import PathosProofs.Store.Intern
public import PathosProofs.Store.Rep
public import MiniCacheSem
public import PathosProofs.Store.Cache
public import PathosProofs.Store.Jumps

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

/-- A constructor whose terms are built strictly, as applications are: a
user operator, whose fields are its indices, or a variable. `construct`
gives the stuck term for one with a stuck field, so no such node holds the
stuck term. -/
def schema.Constructor.Strict (c : schema.Constructor) : Prop :=
  c.is_user = ok true ∨ c.embedding = ok Embedding.Var

/-- Data whose handles are handles of `nodes`, an application being of two
terms that are not stuck, a node having as many fields as its constructor
takes, none of them stuck if the constructor is strict. -/
def TermData.Wf (nodes : List TermData) : TermData → Prop
  | TermData.Apply f a =>
    f.val < nodes.length ∧ a.val < nodes.length ∧
    nodes[f.val]! ≠ TermData.Stuck ∧ nodes[a.val]! ≠ TermData.Stuck
  | TermData.Node c fields =>
    (∀ x ∈ fields.val, x.val < nodes.length) ∧
    (∃ n : Std.Usize, c.arity = ok n ∧ n.val = fields.length) ∧
    (c.Strict → ∀ x ∈ fields.val, nodes[x.val]! ≠ TermData.Stuck)
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
  · refine ⟨fun x hx => by have := h.1 x hx; omega, h.2.1, fun hc x hx => ?_⟩
    rw [hget _ (h.1 x hx)]; exact h.2.2 hc x hx

/-- The terms of a store are well formed: the first is the stuck term, and
a term's data refers to earlier terms only. -/
structure Store.Wf (s : Store) : Prop where
  nonempty : 0 < s.nodes.length
  stuck0 : s.nodes.val[0]! = TermData.Stuck
  wf : ∀ t : Nat, t < s.nodes.length → (s.nodes.val[t]!).Wf (s.nodes.val.take t)

/-- What an entry of the cache of program results says, in a store whose
terms are `nodes`: its result is a handle of the program's result on what
its arguments stand for. What that is for each program is the generated
table `ProgramSem` (`MiniCacheSem`). -/
def EntryOK (nodes : List TermData) (e : cache.ProgramEntry) : Prop :=
  ProgramSem nodes e.program.val e.args.val e.result

theorem EntryOK.mono {nodes nodes' : List TermData} {e : cache.ProgramEntry}
    (hpre : nodes <+: nodes') (h : EntryOK nodes e) : EntryOK nodes' e :=
  ProgramSem.mono hpre h

/-- The type caches stand in the table `ProgramSem` as programs of one
argument, under ids that no `u32` program id can be: `$eo_typeof`'s
(`TypeCacheKind::Eunoia`) is `2^32`, `$smtx_typeof`'s (`Smt`) `2^32 + 1`.
The generated `MiniCacheSem` uses the same numbers. -/
def typeSemId : cache.TypeCacheKind → Nat
  | cache.TypeCacheKind.Eunoia => 4294967296
  | cache.TypeCacheKind.Smt => 4294967297

/-- The slot of a row of the type cache for one kind. -/
def cache.TypeEntry.slot (e : cache.TypeEntry) : cache.TypeCacheKind → Option Term
  | cache.TypeCacheKind.Eunoia => e.eo
  | cache.TypeCacheKind.Smt => e.smt

/-- What the type cache says, in a store whose terms are `nodes`: the row
of a handle holds, in each slot that is filled, a handle of that program's
result on what the handle stands for. -/
def TypesOK (nodes : List TermData) (types : List cache.TypeEntry) : Prop :=
  ∀ (t : Term) (e : cache.TypeEntry), types[(t.val : Nat)]? = some e →
    ∀ k r, e.slot k = some r → ProgramSem nodes (typeSemId k) [t] r

theorem TypesOK.mono {nodes nodes' : List TermData} {types : List cache.TypeEntry}
    (hpre : nodes <+: nodes') (h : TypesOK nodes types) : TypesOK nodes' types :=
  fun t e he k r hr => ProgramSem.mono hpre (h t e he k r hr)

/-- The number of filled slots of the type cache. -/
def typesFilled (types : List cache.TypeEntry) : Nat :=
  (types.map (fun e => (if e.eo.isSome then 1 else 0) + (if e.smt.isSome then 1 else 0))).sum

theorem typesFilled_le (types : List cache.TypeEntry) : typesFilled types ≤ 2 * types.length := by
  unfold typesFilled
  induction types with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    split <;> split <;> omega

theorem typesFilled_extend (a : List cache.TypeEntry) (k : Nat) :
    typesFilled (a ++ List.replicate k { eo := none, smt := none }) = typesFilled a := by
  unfold typesFilled
  simp [List.map_replicate, List.sum_replicate]

theorem TypesOK.extend {nodes : List TermData} {a b : cache.Caches}
    (hx : TypesExtend a b) (h : TypesOK nodes a.types.val) : TypesOK nodes b.types.val := by
  obtain ⟨⟨k, hk⟩, _⟩ := hx
  intro t e he kk r hr
  rw [hk] at he
  by_cases ht : (t.val : Nat) < a.types.val.length
  · rw [List.getElem?_append_left ht] at he
    exact h t e he kk r hr
  · rw [List.getElem?_append_right (by omega)] at he
    have := List.mem_of_getElem? he
    simp only [List.mem_replicate] at this
    rw [this.2] at hr
    cases kk <;> simp [cache.TypeEntry.slot] at hr

/-- The cache of program results is well formed and every entry is right,
and so is every filled slot of the type cache. -/
structure CacheInv (s : Store) : Prop where
  wf : CacheWf s.caches.programs
  entries : ∀ e ∈ s.caches.programs.entries.val, EntryOK s.nodes.val e
  types : TypesOK s.nodes.val s.caches.types.val
  /-- The count of entries that `type_insert` keeps is at most the number
  of filled slots, so it never overflows. -/
  count : s.caches.stats.type_entries.val ≤ typesFilled s.caches.types.val

/-- The invariant of the store. -/
structure Store.Inv (s : Store) : Prop where
  table : StoreInv s
  terms : s.Wf
  cache : CacheInv s
  /-- The jump pointers of `state_nth` lead where the walk down a state
  list would (Store/Jumps.lean). -/
  jumps : JumpsOK s.nodes.val s.state_jumps.val

theorem Store.Wf.data {s : Store} (h : s.Wf) (t : Nat) (ht : t < s.nodes.length) :
    (s.nodes.val[t]!).Wf s.nodes.val :=
  (h.wf t ht).mono (List.take_prefix _ _)

/-- `intern` of well-formed data keeps the store's invariant. -/
theorem Store.intern_inv (s : Store) (data : TermData) (hinv : s.Inv)
    (hd : data.Wf s.nodes.val) (h64 : Platform64) :
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
    have hcache : CacheInv s' := by
      have hp := hext.2.2.2.2.2.1
      constructor
      · rw [hp]; exact hinv.cache.wf
      · intro e he
        rw [hp] at he
        exact (hinv.cache.entries e he).mono hext.1
      · exact (hinv.cache.types.mono hext.1).extend hext.2.2.2.2.2.2
      · obtain ⟨⟨k, hk⟩, hst⟩ := hext.2.2.2.2.2.2
        rw [hst, hk, typesFilled_extend]; exact hinv.cache.count
    have hjumps : JumpsOK s'.nodes.val s'.state_jumps.val := by
      rw [hext.2.2.2.2.1]; exact hinv.jumps.mono hext.1
    refine ⟨⟨htable, ?_, hcache, hjumps⟩, hext, hlt, hdata⟩
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
theorem Store.apply_spec (s : Store) (f a : Term) (hinv : s.Inv) (h64 : Platform64) :
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

theorem Store.check_handles_loop_spec (s : Store) (args : Slice Term) (i : Std.Usize) :
    Store.check_handles_loop s args i ⦃ r =>
      match r with
      | core.result.Result.Ok _ =>
        ∀ j : Nat, i.val ≤ j → j < args.length → (args.val[j]! : Term).val < s.nodes.length
      | core.result.Result.Err _ => True ⦄div := by
  revert i
  apply Store.check_handles_loop.fixpoint_induct s args
    (motive := fun f => ∀ i : Std.Usize, f i ⦃ r =>
      match r with
      | core.result.Result.Ok _ =>
        ∀ j : Nat, i.val ≤ j → j < args.length → (args.val[j]! : Term).val < s.nodes.length
      | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih i
    simp only
    split
    · rename_i hlt
      step as ⟨t, ht⟩
      rw [Store.view_eq]
      have hilt : i.val < args.val.length := by scalar_tac
      have hta : args.val[i.val]! = t := by rw [ht]; exact getElem!_eq _ _ hilt
      by_cases hv : t.val < s.nodes.length
      · simp only [hv, ite_true, core.result.Result.Insts.CoreOpsTry.branch]
        step as ⟨i2, hi2⟩
        apply WP.dspec_mono (ih i2)
        intro r hr
        cases r with
        | Err e => trivial
        | Ok u =>
          simp only at hr ⊢
          intro j hj hjl
          by_cases hji : j = i.val
          · subst hji; rw [hta]; exact hv
          · exact hr j (by omega) hjl
      · simp [hv, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · rename_i hge
      simp only [WP.dspec_ok]
      intro j hj hjl
      exfalso; scalar_tac

theorem schema.Constructor.arity_ok (c : schema.Constructor) : ∃ n, c.arity = ok n := by
  cases c <;> exact ⟨_, rfl⟩

/-- `stuck_or_foreign` on a handle of the store: whether its data is the
stuck term. -/
theorem Store.stuck_or_foreign_lt (s : Store) (t : Term) (h : t.val < s.nodes.length) :
    Store.stuck_or_foreign s t = ok (s.nodes.val[t.val]!).isStuck := by
  unfold Store.stuck_or_foreign
  rw [Store.view_eq]
  simp only [h, ite_true, Std.bind_ok]
  cases s.nodes.val[t.val]! <;> rfl

/-- `any_stuck` on handles of the store: whether the data of one of them is
the stuck term. -/
theorem Store.any_stuck_loop_lt (s : Store) (args : Slice Term)
    (hlt : ∀ a ∈ args.val, a.val < s.nodes.length) :
    ∀ (k : Nat) (any : Bool) (i : Std.Usize), args.length - i.val = k →
      Store.any_stuck_loop s args any i =
        ok (any || (args.val.drop i.val).any (fun a => (s.nodes.val[a.val]!).isStuck)) := by
  intro k
  induction k with
  | zero =>
    intro any i hk
    unfold Store.any_stuck_loop
    have hle : args.val.length ≤ i.val := by simp only [Slice.length] at hk; omega
    have hge : ¬ i < Slice.len args := by
      intro h
      have : i.val < (Slice.len args).val := h
      simp [Slice.len] at this; omega
    have hd : args.val.drop i.val = [] := List.drop_eq_nil_of_le hle
    simp [hge, hd]
  | succ k ih =>
    intro any i hk
    unfold Store.any_stuck_loop
    have hilt : i.val < args.val.length := by simp only [Slice.length] at hk; omega
    have hlt' : i < Slice.len args := by
      show i.val < (Slice.len args).val
      simp [Slice.len]; exact hilt
    have hidx : Slice.index_usize args i = ok (args.val[i.val]'hilt) := by
      simp [Slice.index_usize, hilt]
    have hd : args.val.drop i.val = (args.val[i.val]'hilt) :: args.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hilt
    have hxmem : (args.val[i.val]'hilt) ∈ args.val := List.getElem_mem hilt
    generalize args.val[i.val]'hilt = x at hidx hd hxmem
    simp only [hlt', ite_true, hidx, Std.bind_ok, Store.stuck_or_foreign_lt s x (hlt x hxmem)]
    obtain ⟨i1, hi1e, hi1v⟩ := spec_returns
      (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hi1e]
    simp only [Std.bind_ok]
    have hk1 : args.length - i1.val = k := by
      simp only [Slice.length] at hk ⊢; simp at hi1v; omega
    have hi1v' : i1.val = i.val + 1 := by simpa using hi1v
    cases hst : (s.nodes.val[x.val]!).isStuck
    · simp only [Bool.false_eq_true, ite_false, Std.bind_ok]
      rw [ih any i1 hk1, hi1v', hd]
      simp only [List.any_cons, hst, Bool.false_or]
    · simp only [ite_true, Std.bind_ok]
      rw [ih true i1 hk1, hi1v', hd]
      simp only [List.any_cons, hst, Bool.true_or, Bool.or_true]

theorem Store.any_stuck_lt (s : Store) (args : Slice Term)
    (hlt : ∀ a ∈ args.val, a.val < s.nodes.length) :
    Store.any_stuck s args =
      ok (args.val.any (fun a => (s.nodes.val[a.val]!).isStuck)) := by
  unfold Store.any_stuck
  rw [Store.any_stuck_loop_lt s args hlt _ false 0#usize rfl]
  simp

/-- Whether the data of one of some handles is the stuck term. -/
theorem any_isStuck_iff (nodes : List TermData) (l : List Term) :
    l.any (fun a => (nodes[a.val]!).isStuck) = true ↔
      ∃ a ∈ l, nodes[a.val]! = TermData.Stuck := by
  simp [List.any_eq_true, TermData.isStuck_iff]

theorem Embedding.eq_data_var :
    Embedding.Insts.CoreCmpPartialEqEmbedding.eq Embedding.Data Embedding.Var = ok false := by
  simp [Embedding.Insts.CoreCmpPartialEqEmbedding.eq, Embedding.read_discriminant]

theorem Embedding.eq_var_var :
    Embedding.Insts.CoreCmpPartialEqEmbedding.eq Embedding.Var Embedding.Var = ok true := by
  simp [Embedding.Insts.CoreCmpPartialEqEmbedding.eq, Embedding.read_discriminant]

theorem schema.Constructor.is_user_ok (c : schema.Constructor) : ∃ b, c.is_user = ok b := by
  cases c <;> exact ⟨_, rfl⟩

/-- The node of `c` with the arguments as its fields, interned. -/
theorem Store.intern_node_spec (s : Store) (c : schema.Constructor) (args : Slice Term)
    (hinv : s.Inv) (h64 : Platform64) (n : Std.Usize) (hn : c.arity = ok n)
    (hlen : n.val = args.val.length) (hlt : ∀ a ∈ args.val, a.val < s.nodes.length)
    (hns : c.Strict → ∀ a ∈ args.val, s.nodes.val[a.val]! ≠ TermData.Stuck) :
    (do
      let v ← alloc.slice.Slice.to_vec Term.Insts.CoreCloneClone args
      Store.intern s (TermData.Node c v)) ⦃ r s' =>
      s'.Inv ∧ s.Extends s' ∧
      match r with
      | core.result.Result.Ok t =>
        t.val < s'.nodes.length ∧
        ∃ v : alloc.vec.Vec Term, v.val = args.val ∧ s'.data t = TermData.Node c v
      | core.result.Result.Err _ => s' = s ⦄div := by
  step with alloc.slice.Slice.to_vec_spec as ⟨v, hv⟩
  · intro x _; rfl
  have hvals : v.val = args.val := by rw [hv]; rfl
  have hwf : (TermData.Node c v).Wf s.nodes.val := by
    refine ⟨?_, ⟨n, hn, ?_⟩, ?_⟩
    · intro x hx; rw [hvals] at hx; exact hlt x hx
    · rw [hlen]; simp [alloc.vec.Vec.length, hvals]
    · intro hc x hx; rw [hvals] at hx; exact hns hc x hx
  apply WP.dspec_mono (Store.intern_inv s (TermData.Node c v) hinv hwf h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext, ?_⟩
  cases r with
  | Err e => exact hres
  | Ok t => exact ⟨hres.1, v, hvals, hres.2⟩

/-- `construct` with a constructor that is plain data, or a variable (which
the store keeps the same way): the node of that constructor with the
arguments as its fields; or, for a strict constructor (a user operator, or
a variable) with a stuck argument, the stuck term, as `apply` gives for an
application of or to the stuck term. -/
theorem Store.construct_data_spec (s : Store) (c : schema.Constructor) (args : Slice Term)
    (hinv : s.Inv) (h64 : Platform64)
    (hemb : c.embedding = ok Embedding.Data ∨ c.embedding = ok Embedding.Var) :
    Store.construct s c args ⦃ r s' =>
      s'.Inv ∧ s.Extends s' ∧
      match r with
      | core.result.Result.Ok t =>
        t.val < s'.nodes.length ∧
        ((c.Strict ∧ (∃ a ∈ args.val, s.nodes.val[a.val]! = TermData.Stuck) ∧
            t = 0#u32 ∧ s' = s) ∨
          ((c.Strict → ∀ a ∈ args.val, s.nodes.val[a.val]! ≠ TermData.Stuck) ∧
            ∃ v : alloc.vec.Vec Term, v.val = args.val ∧ s'.data t = TermData.Node c v))
      | core.result.Result.Err _ => s' = s ⦄div := by
  unfold Store.construct
  obtain ⟨n, hn⟩ := schema.Constructor.arity_ok c
  rw [hn]
  simp only [Std.bind_ok]
  by_cases harity : (n != args.len) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true harity)]
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Extends.refl s, trivial⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false harity)]
    step with Store.check_handles_loop_spec as ⟨r, hr⟩
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact ⟨hinv, Store.Extends.refl s⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      have hlt : ∀ a ∈ args.val, a.val < s.nodes.length := by
        intro a ha
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
        have := hr j (Nat.zero_le _) hj
        rwa [getElem!_eq _ _ hj] at this
      have hlen : n.val = args.val.length := by
        have : n.val = args.val.length := by simpa using harity
        exact this
      have hpos : (0 : Nat) < s.nodes.length := hinv.terms.nonempty
      obtain ⟨b, hb⟩ := schema.Constructor.is_user_ok c
      -- the strict path: the stuck term if an argument is stuck, else the node
      have hstrict : c.Strict →
          (do
            let b1 ← Store.any_stuck s args
            if b1 then
              let t ← Store.stuck s
              ok (core.result.Result.Ok t, s)
            else
              let v ← alloc.slice.Slice.to_vec Term.Insts.CoreCloneClone args
              Store.intern s (TermData.Node c v)) ⦃ r s' =>
          s'.Inv ∧ s.Extends s' ∧
          match r with
          | core.result.Result.Ok t =>
            t.val < s'.nodes.length ∧
            ((c.Strict ∧ (∃ a ∈ args.val, s.nodes.val[a.val]! = TermData.Stuck) ∧
                t = 0#u32 ∧ s' = s) ∨
              ((c.Strict → ∀ a ∈ args.val, s.nodes.val[a.val]! ≠ TermData.Stuck) ∧
                ∃ v : alloc.vec.Vec Term, v.val = args.val ∧ s'.data t = TermData.Node c v))
          | core.result.Result.Err _ => s' = s ⦄div := by
        intro hc
        rw [Store.any_stuck_lt s args hlt]
        simp only [Std.bind_ok]
        cases hb1 : args.val.any (fun a => (s.nodes.val[a.val]!).isStuck)
        · simp only [Bool.false_eq_true, ite_false]
          have hns : ∀ a ∈ args.val, s.nodes.val[a.val]! ≠ TermData.Stuck := by
            intro a ha h
            have : args.val.any (fun a => (s.nodes.val[a.val]!).isStuck) = true :=
              (any_isStuck_iff s.nodes.val args.val).mpr ⟨a, ha, h⟩
            rw [hb1] at this; cases this
          apply WP.dspec_mono (Store.intern_node_spec s c args hinv h64 n hn hlen hlt
            (fun _ => hns))
          rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
          refine ⟨hinv', hext, ?_⟩
          cases r with
          | Err e => exact hres
          | Ok t => exact ⟨hres.1, Or.inr ⟨fun _ => hns, hres.2⟩⟩
        · simp only [ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Extends.refl s, by simpa using hpos,
            Or.inl ⟨hc, (any_isStuck_iff s.nodes.val args.val).mp hb1, by simp⟩⟩
      -- the plain path: the node, the constructor not being strict
      have hplain : ¬ c.Strict →
          (do
            let v ← alloc.slice.Slice.to_vec Term.Insts.CoreCloneClone args
            Store.intern s (TermData.Node c v)) ⦃ r s' =>
          s'.Inv ∧ s.Extends s' ∧
          match r with
          | core.result.Result.Ok t =>
            t.val < s'.nodes.length ∧
            ((c.Strict ∧ (∃ a ∈ args.val, s.nodes.val[a.val]! = TermData.Stuck) ∧
                t = 0#u32 ∧ s' = s) ∨
              ((c.Strict → ∀ a ∈ args.val, s.nodes.val[a.val]! ≠ TermData.Stuck) ∧
                ∃ v : alloc.vec.Vec Term, v.val = args.val ∧ s'.data t = TermData.Node c v))
          | core.result.Result.Err _ => s' = s ⦄div := by
        intro hc
        apply WP.dspec_mono (Store.intern_node_spec s c args hinv h64 n hn hlen hlt
          (fun h => absurd h hc))
        rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
        refine ⟨hinv', hext, ?_⟩
        cases r with
        | Err e => exact hres
        | Ok t => exact ⟨hres.1, Or.inr ⟨fun h => absurd h hc, hres.2⟩⟩
      rcases hemb with hemb | hemb <;> rw [hemb] <;> simp only [Std.bind_ok, hb]
      · cases b
        · simp only [Bool.false_eq_true, ite_false, Embedding.eq_data_var, Std.bind_ok]
          apply hplain
          rintro (h | h) <;> simp_all
        · simp only [ite_true]
          exact hstrict (Or.inl hb)
      · cases b
        · simp only [Bool.false_eq_true, ite_false, Embedding.eq_var_var, Std.bind_ok, ite_true]
          exact hstrict (Or.inr hemb)
        · simp only [ite_true]
          exact hstrict (Or.inl hb)

theorem Store.destruct_literal_data (l : lit.Lit) :
    Store.destruct_literal Embedding.Data l = ok (Hit.Done none) := by
  unfold Store.destruct_literal
  cases l <;> simp

theorem Store.destruct_literal_var (l : lit.Lit) :
    Store.destruct_literal Embedding.Var l = ok (Hit.Done none) := by
  unfold Store.destruct_literal
  cases l <;> simp [Embedding.Insts.CoreCmpPartialEqEmbedding.eq, Embedding.read_discriminant]

theorem alloc.vec.CloneVec.clone_terms (v : alloc.vec.Vec Term) :
    alloc.vec.CloneVec.clone Term.Insts.CoreCloneClone v = ok v := by
  unfold alloc.vec.CloneVec.clone
  have h : ∀ x ∈ v.slice.val, Term.Insts.CoreCloneClone.clone x = ok x := fun _ _ => rfl
  obtain ⟨s', hs, heq⟩ := spec_returns (Slice.clone_spec h)
  simp only [Term.Insts.CoreCloneClone] at hs ⊢
  rw [hs]
  simp [← heq]

/-- `destruct` with a constructor that is plain data, or a variable: the
fields of a node of that constructor, and nothing for any other term. -/
theorem Store.destruct_data_eq (s : Store) (c : schema.Constructor) (t : Term)
    (hemb : c.embedding = ok Embedding.Data ∨ c.embedding = ok Embedding.Var) :
    Store.destruct s c t = ok (
      (if t.val < s.nodes.length then
        core.result.Result.Ok (match s.data t with
          | TermData.Node d fields => if d = c then some fields else none
          | _ => none)
      else core.result.Result.Err CheckError.InvalidHandle), s) := by
  unfold Store.destruct
  rcases hemb with hemb | hemb <;> rw [hemb] <;> simp only [Std.bind_ok]
  all_goals
  rw [Store.view_eq]
  by_cases h : t.val < s.nodes.length
  · simp only [h, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Store.data]
    cases hd : s.nodes.val[t.val]! with
    | Literal l => simp [Store.destruct_literal_data, Store.destruct_literal_var]
    | Node d fields =>
      obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec c
      obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
      simp only [h1, h2, Std.bind_ok]
      by_cases hdc : d = c
      · subst hdc
        have : n1 = n2 := by rw [h1] at h2; simpa using h2
        simp [this, alloc.vec.CloneVec.clone_terms]
      · have : n1 ≠ n2 := by
          intro heq; subst heq; exact hdc (schema.Constructor.code_inj h2 h1)
        simp [this, hdc]
    | _ => simp
  · simp [h, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end pathos_compiled_checker
