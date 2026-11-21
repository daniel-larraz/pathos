module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Store.Jumps
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import MiniEmbed
import all Aeneas.Data.List.List
import all Aeneas.Std.Core.Core
import all Aeneas.Std.Scalar.SaturatingOps

/-!
# The state lookup with jump pointers (`Store::state_nth`)

The generator compiles `$eo_state_proven_nth` to a call of the runtime's
`Store::state_nth`, which finds the index-th element of a state list with
Myers's jump pointers (the side table `state_jumps`), then of the generated
`$eo_StateObj_proven` on it. Here: what `state_nth` gives, against logos's
recursive `__eo_state_proven_nth`, on the store's invariant `JumpsOK`
(Store/Jumps.lean), which every operation keeps.

The statements are partial, as every spec here: an error satisfies them.
So the budget that `state_nth` charges (the runtime charges what the walk
would) needs no proof that it equals the walk's; only that the store grows
(`Store.Grows`, whose budget never goes up).
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-! ## logos's side -/

/-- The number of objects of a state. -/
def stateLen : Eo.CState → Nat
  | Eo.CState.cons _ s => stateLen s + 1
  | _ => 0

/-- The state after dropping `k` objects. -/
def stateDrop : Eo.CState → Nat → Eo.CState
  | s, 0 => s
  | Eo.CState.cons _ s, k + 1 => stateDrop s k
  | s, _ + 1 => s

theorem state_proven_nth_cons_zero (so : Eo.CStateObj) (s : Eo.CState) :
    Eo.__eo_state_proven_nth (Eo.CState.cons so s) 0 = Eo.__eo_StateObj_proven so := by
  simp [Eo.__eo_state_proven_nth]

theorem state_proven_nth_cons_ne (so : Eo.CStateObj) (s : Eo.CState) (n : Int) (hn : n ≠ 0) :
    Eo.__eo_state_proven_nth (Eo.CState.cons so s) n = Eo.__eo_state_proven_nth s (n - 1) := by
  have hsub : Eo.native_zplus n (Eo.native_zneg 1) = n - 1 := by
    show n + -1 = n - 1; omega
  rw [← hsub]
  conv => lhs; unfold Eo.__eo_state_proven_nth
  split
  all_goals first
    | rfl
    | (exfalso; simp_all; done)
    | (simp_all; done)

theorem state_proven_nth_not_cons (s : Eo.CState) (n : Int)
    (h : ∀ so s', s ≠ Eo.CState.cons so s') : Eo.__eo_state_proven_nth s n = Eo.Term.Boolean true := by
  cases s with
  | cons so s' => exact absurd rfl (h so s')
  | _ => simp [Eo.__eo_state_proven_nth]

/-- The `k`-th object, for `k` below the length. -/
theorem state_proven_nth_drop (s : Eo.CState) (k : Nat) (so : Eo.CStateObj) (s' : Eo.CState)
    (h : stateDrop s k = Eo.CState.cons so s') :
    Eo.__eo_state_proven_nth s k = Eo.__eo_StateObj_proven so := by
  induction k generalizing s with
  | zero => simp only [stateDrop] at h; subst h; exact state_proven_nth_cons_zero so s'
  | succ k ih =>
    cases s with
    | cons so0 s0 =>
      rw [state_proven_nth_cons_ne so0 s0 ((k + 1 : Nat) : Int) (by omega)]
      have : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by push_cast; ring
      rw [this]; exact ih s0 (by simpa [stateDrop] using h)
    | _ => simp [stateDrop] at h

/-- A negative index, or one past the end, gives `true`. -/
theorem state_proven_nth_out (s : Eo.CState) (n : Int) (h : n < 0 ∨ (stateLen s : Int) ≤ n) :
    Eo.__eo_state_proven_nth s n = Eo.Term.Boolean true := by
  induction s generalizing n with
  | cons so s ih =>
    have hn : n ≠ 0 := by simp only [stateLen] at h; omega
    rw [state_proven_nth_cons_ne _ _ _ hn]
    exact ih _ (by simp only [stateLen] at h; omega)
  | _ => simp [Eo.__eo_state_proven_nth]

/-! ## Handles of states -/

/-- A handle of `cons so s` is a `cons` node whose fields stand for `so` and `s`. -/
theorem Rep.state_cons {nodes : List TermData} {t : Nat} {so : Eo.CStateObj} {s : Eo.CState}
    (h : Rep nodes t (Eo.CState.cons so s)) :
    ∃ v : alloc.vec.Vec Term, ∃ a b : Term, t < nodes.length ∧
      nodes[t]! = TermData.Node stateCons v ∧ v.val = [a, b] ∧
      Rep nodes a.val so ∧ Rep nodes b.val s := by
  obtain ⟨hh, hemb⟩ := h
  change Holds nodes t (Embed.enc_CState (Eo.CState.cons so s)) at hh
  simp only [Embed.enc_CState] at hh
  cases hh with
  | node _ _ v xs hlt hd hl =>
    generalize hvv : v.val = l at hl
    cases hl with
    | cons a hs x xs ha hl =>
      cases hl with
      | cons b hs y ys hb hl =>
        cases hl with
        | nil =>
          obtain ⟨e1, e2⟩ := hemb
          exact ⟨v, a, b, hlt, hd, hvv, ⟨ha, e1⟩, ⟨hb, e2⟩⟩

/-- A handle of a state that is no `cons` is no `cons` node. -/
theorem Rep.state_not_cons {nodes : List TermData} {t : Nat} {s : Eo.CState}
    (h : Rep nodes t s) (hs : ∀ so s', s ≠ Eo.CState.cons so s') : ∀ u, ¬ StateTail nodes t u := by
  intro u ⟨v, _, hd, _, _⟩
  obtain ⟨hh, _⟩ := h
  cases s with
  | cons so s' => exact hs so s' rfl
  | nil =>
    change Holds nodes t (Embed.enc_CState Eo.CState.nil) at hh
    simp only [Embed.enc_CState] at hh
    cases hh with | node _ _ v' _ _ hd' _ => rw [hd] at hd'; cases hd'
  | Stuck =>
    change Holds nodes t (Embed.enc_CState Eo.CState.Stuck) at hh
    simp only [Embed.enc_CState] at hh
    cases hh with | node _ _ v' _ _ hd' _ => rw [hd] at hd'; cases hd'

/-- The tail of a handle of `cons so s` stands for `s`. -/
theorem Rep.state_tail {nodes : List TermData} {t u : Nat} {so : Eo.CStateObj} {s : Eo.CState}
    (h : Rep nodes t (Eo.CState.cons so s)) (ht : StateTail nodes t u) : Rep nodes u s := by
  obtain ⟨v, a, b, _, hd, hv, _, hb⟩ := h.state_cons
  obtain ⟨v', _, hd', _, hu⟩ := ht
  rw [hd] at hd'; cases hd'
  rw [← hu, hv]; exact hb

/-- Going down a handle's tails: the depth is the state's length, and `k`
tails down stands for the state with `k` objects dropped. -/
theorem Rep.state_depth {nodes : List TermData} {t d : Nat} {s : Eo.CState}
    (h : Rep nodes t s) (hd : StateDepth nodes t d) : d = stateLen s := by
  induction hd generalizing s with
  | stop t _ hno =>
    cases s with
    | cons so s' =>
      obtain ⟨v, a, b, hlt, hdat, hv, _, _⟩ := h.state_cons
      exact absurd ⟨v, hlt, hdat, by simp [hv], by simp [hv]⟩ (hno b.val)
    | _ => rfl
  | step t u d htl _ ih =>
    cases s with
    | cons so s' => simp only [stateLen]; rw [ih (h.state_tail htl)]
    | _ => exact absurd htl (h.state_not_cons (by intro _ _ h; cases h) u)

theorem Rep.state_down {nodes : List TermData} {t k v : Nat} {s : Eo.CState}
    (h : Rep nodes t s) (hk : StateDown nodes t k v) : Rep nodes v (stateDrop s k) := by
  induction hk generalizing s with
  | zero t => simpa [stateDrop] using h
  | succ t u k v htl _ ih =>
    cases s with
    | cons so s' => simpa [stateDrop] using ih (h.state_tail htl)
    | _ => exact absurd htl (h.state_not_cons (by intro _ _ h; cases h) u)

/-! ## The table of jump pointers -/

/-- The entry of a handle, where it is filled. -/
def jumpOf (jumps : List (Std.U32 × Term)) (t : Nat) : Option (Std.U32 × Term) :=
  match jumps[t]? with
  | some e => if 0 < e.1.val then some e else none
  | none => none

theorem Store.state_jump_spec (s : Store) (t : Term) :
    Store.state_jump s t ⦃ r => r = jumpOf s.state_jumps.val t.val ⦄ := by
  unfold Store.state_jump jumpOf
  by_cases hlt : (t.val : Nat) < s.state_jumps.val.length
  · rw [List.getElem?_eq_getElem hlt]
    step*
    all_goals
      have hit : (i.val : Nat) = t.val := by rw [i_post]; scalar_tac
      have h1 := congrArg Prod.fst i2_post
      simp only [hit] at h1
      simp_all
  · rw [List.getElem?_eq_none (by omega)]
    step*
    all_goals
      have hit : (i.val : Nat) = t.val := by rw [i_post]; scalar_tac
      simp_all [alloc.vec.Vec.len, alloc.vec.Vec.length]
      try scalar_tac

theorem JumpsOK.of_jumpOf {nodes : List TermData} {jumps : List (Std.U32 × Term)}
    (h : JumpsOK nodes jumps) {t : Nat} {e : Std.U32 × Term} (he : jumpOf jumps t = some e) :
    0 < e.1.val ∧ StateDepth nodes t e.1.val ∧
      ∃ k, 1 ≤ k ∧ k ≤ e.1.val ∧ StateDown nodes t k e.2.val := by
  unfold jumpOf at he
  cases he' : jumps[t]? with
  | none => rw [he'] at he; cases he
  | some e' =>
    rw [he'] at he
    simp only at he
    by_cases hpos : 0 < e'.1.val
    · rw [if_pos hpos] at he
      simp only [Option.some.injEq] at he; subst he
      exact ⟨hpos, h t _ he' hpos⟩
    · simp [hpos] at he

/-- The depth an entry records, or 0. -/
def jumpDepth (jumps : List (Std.U32 × Term)) (t : Nat) : Std.U32 :=
  match jumpOf jumps t with
  | some e => e.1
  | none => 0#u32

theorem Store.state_jump_depth_spec (s : Store) (t : Term) :
    Store.state_jump_depth s t ⦃ r => r = jumpDepth s.state_jumps.val t.val ⦄ := by
  unfold Store.state_jump_depth jumpDepth
  step with Store.state_jump_spec as ⟨o, ho⟩
  subst ho
  cases jumpOf s.state_jumps.val t.val with
  | none => simp
  | some p => obtain ⟨d, j⟩ := p; simp

/-- The depth an entry records is the depth, where the entry is filled. -/
theorem JumpsOK.jumpDepth {nodes : List TermData} {jumps : List (Std.U32 × Term)}
    (h : JumpsOK nodes jumps) {t d : Nat} (hd : StateDepth nodes t d) :
    (jumpDepth jumps t).val = 0 ∨ (jumpDepth jumps t).val = d := by
  unfold pathos_compiled_checker.jumpDepth
  split
  · rename_i e he
    obtain ⟨_, hd', _⟩ := h.of_jumpOf he
    exact Or.inr (hd'.functional hd)
  · exact Or.inl rfl

/-- `state_tail` of a handle: its tail, which is an earlier handle, where it
is a `cons` node; `none` where it is a handle and no `cons` node. -/
theorem Store.state_tail_spec (s : Store) (hinv : s.Inv) (t : Term) :
    Store.state_tail s stateCons t ⦃ r =>
      match r with
      | core.result.Result.Ok (some u) => StateTail s.nodes.val t.val u.val ∧ u.val < t.val
      | core.result.Result.Ok none =>
        t.val < s.nodes.val.length ∧ ∀ u, ¬ StateTail s.nodes.val t.val u
      | core.result.Result.Err _ => True ⦄ := by
  unfold Store.state_tail
  rw [Store.view_eq]
  by_cases hlt : t.val < s.nodes.length
  · simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    have hlt' : t.val < s.nodes.val.length := hlt
    have hno : ∀ u, ¬ StateTail s.nodes.val t.val u → True := fun _ _ => trivial
    cases hd : s.nodes.val[t.val]! with
    | Node c fields =>
      simp only
      obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec c
      obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec stateCons
      rw [h1, h2]
      simp only [Std.bind_ok]
      by_cases hc : n1 = n2
      · subst hc
        have hcc := schema.Constructor.code_inj h1 h2
        subst hcc
        simp only [ite_true]
        by_cases hl : fields.val.length = 2
        · have hl2 : alloc.vec.Vec.len fields = 2#usize := by
            simp [alloc.vec.Vec.len]; scalar_tac
          simp only [hl2, ite_true]
          step as ⟨u, hu⟩
          have hwf := hinv.terms.wf t.val hlt
          rw [hd] at hwf
          have hmem : u ∈ fields.val := by rw [hu]; exact List.getElem_mem _
          have hult := hwf.1 u hmem
          simp only [List.length_take] at hult
          refine ⟨⟨fields, hlt', hd, hl, ?_⟩, by omega⟩
          rw [hu, getElem!_pos fields.val 1 (by omega)]
        · have hl2 : alloc.vec.Vec.len fields ≠ 2#usize := by
            intro h; apply hl; simp [alloc.vec.Vec.len] at h; scalar_tac
          simp only [hl2, ite_false, WP.spec_ok]
          refine ⟨by first | trivial | exact hlt', fun u ⟨f', _, hd', hl', _⟩ => ?_⟩
          rw [hd] at hd'; cases hd'; exact hl hl'
      · simp only [hc, ite_false, WP.spec_ok]
        refine ⟨by first | trivial | exact hlt', fun u ⟨f', _, hd', _, _⟩ => ?_⟩
        rw [hd] at hd'; cases hd'; rw [h1] at h2; exact hc (by simpa using h2)
    | _ =>
      simp only [WP.spec_ok]
      refine ⟨by first | trivial | exact hlt', fun u ⟨f', _, hd', _, _⟩ => ?_⟩
      rw [hd] at hd'; cases hd'
  · simp [hlt, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem JumpsOK.resize {nodes : List TermData} {l : List (Std.U32 × Term)} (h : JumpsOK nodes l)
    (n : Nat) : JumpsOK nodes (l.resize n (0#u32, 0#u32)) := by
  intro t e he hpos
  simp only [List.resize, ge_iff_le, zero_le, ite_true] at he
  by_cases ht : t < (l.take n).length
  · rw [List.getElem?_append_left ht, List.getElem?_take] at he
    split at he
    · exact h t e he hpos
    · cases he
  · rw [List.getElem?_append_right (by omega)] at he
    have := List.mem_of_getElem? he
    simp only [List.mem_replicate] at this
    rw [this.2] at hpos; simp at hpos

theorem JumpsOK.set {nodes : List TermData} {l : List (Std.U32 × Term)} (h : JumpsOK nodes l)
    (i : Nat) (e : Std.U32 × Term) (he : JumpOK nodes i e) : JumpsOK nodes (l.set i e) := by
  intro t e' he'
  rw [List.getElem?_set] at he'
  split at he'
  · rename_i hit; subst hit
    split at he'
    · cases he'; exact he
    · cases he'
  · exact h t e' he'

/-- `set_state_jump` writes one entry: an entry that is right keeps the
table right. -/
theorem Store.set_state_jump_spec (s : Store) (t : Term) (e : Std.U32 × Term) (h64 : Platform64)
    (hj : JumpsOK s.nodes.val s.state_jumps.val) (he : JumpOK s.nodes.val t.val e) :
    Store.set_state_jump s t e ⦃ s' => ∃ v : alloc.vec.Vec (Std.U32 × Term),
      s' = { s with state_jumps := v } ∧ JumpsOK s.nodes.val v.val ⦄ := by
  unfold Store.set_state_jump
  step as ⟨i, hi⟩
  have hit : (i.val : Nat) = t.val := by rw [hi]; scalar_tac
  have hset : ∀ v : alloc.vec.Vec (Std.U32 × Term), JumpsOK s.nodes.val v.val →
      t.val < v.val.length →
      (do
        let (_, index_mut_back) ← v.index_mut_usize i
        ok ({ s with state_jumps := index_mut_back e } : Store)) ⦃ s' =>
        ∃ v : alloc.vec.Vec (Std.U32 × Term),
          s' = { s with state_jumps := v } ∧ JumpsOK s.nodes.val v.val ⦄ := by
    intro v hv hlt
    step with alloc.vec.Vec.index_mut_usize_spec v i (by simp only [alloc.vec.Vec.length]; omega)
      as ⟨x, back, hx, hback⟩
    refine ⟨_, rfl, ?_⟩
    rw [hback, alloc.vec.Vec.set_val_eq, hit]
    exact hv.set _ e he
  split
  · rename_i hle
    have hmax : (2 : Nat) ^ 40 ≤ Usize.max := h64
    have hbound : (i.val : Nat) + 1 ≤ Usize.max := by
      have : (t.val : Nat) < 2 ^ 32 := t.hBounds
      omega
    step as ⟨i2, hi2⟩
    step with alloc.vec.Vec.resize_spec (BuiltinClone (Std.U32 × Term)) s.state_jumps _ (0#u32, 0#u32) (by simp [BuiltinClone]) as ⟨v, hv⟩
    apply hset v (by rw [hv]; exact hj.resize _)
    rw [hv, List.resize_length]; omega
  · rename_i hle
    simp only [Std.bind_ok]
    apply hset _ hj
    simp only [alloc.vec.Vec.len, not_le] at hle; scalar_tac


/-! ## The walk's stack -/

/-- The pairs `(node, tail)` from `t` down to `x`, in the order the walk
pushes them. -/
inductive Chain (nodes : List TermData) : Nat → List (Term × Term) → Nat → Prop
  | nil (t : Nat) : Chain nodes t [] t
  | snoc (t : Nat) (ps : List (Term × Term)) (y u : Term) :
      Chain nodes t ps y.val → StateTail nodes y.val u.val → Chain nodes t (ps ++ [(y, u)]) u.val

theorem Chain.unsnoc {nodes : List TermData} {t x : Nat} {ps : List (Term × Term)} {q : Term × Term}
    (h : Chain nodes t (ps ++ [q]) x) :
    Chain nodes t ps q.1.val ∧ StateTail nodes q.1.val q.2.val ∧ x = q.2.val := by
  generalize hl : ps ++ [q] = l at h
  cases h with
  | nil => simp at hl
  | snoc ps' y u hc ht =>
    have := List.append_inj' hl rfl
    obtain ⟨rfl, hq⟩ := this
    simp only [List.cons.injEq, and_true] at hq
    subst hq
    exact ⟨hc, ht, rfl⟩

theorem Chain.nil_eq {nodes : List TermData} {t x : Nat} (h : Chain nodes t [] x) : x = t := by
  generalize hl : ([] : List (Term × Term)) = l at h
  cases h with
  | nil => rfl
  | snoc => simp at hl

/-- The stack's contents: the first `len` items. -/
def stk (p : table.PairStack) : List (Term × Term) := p.items.val.take p.len.val

theorem table.PairStack.pop_spec (p : table.PairStack) (h : p.len.val ≤ p.items.val.length) :
    table.PairStack.pop p ⦃ r p' =>
      p'.len.val ≤ p'.items.val.length ∧
      match r with
      | none => stk p = []
      | some q => stk p = stk p' ++ [q] ⦄ := by
  unfold table.PairStack.pop
  split
  · rename_i h0
    have hz : p.len.val = 0 := by scalar_tac
    simp [stk, hz, h]
  · rename_i h0
    have hpos : 0 < p.len.val := by
      have : p.len.val ≠ 0 := by intro hz; apply h0; scalar_tac
      omega
    step as ⟨i, hi⟩
    step as ⟨q, hq⟩
    have hi' : i.val + 1 = p.len.val := by scalar_tac
    simp only [WP.spec_ok, WP.uncurry'_pair, stk]
    refine ⟨by omega, ?_⟩
    rw [← hi', List.take_succ_eq_append_getElem (by omega)]
    congr 2
    all_goals (rw [hq]; try simp [alloc.vec.Vec.length])

theorem table.PairStack.new_spec :
    table.PairStack.new ⦃ p => p.len.val = 0 ∧ p.items.val = [] ⦄ := by
  unfold table.PairStack.new; simp

/-- `push` on a stack whose items are all in use (the walk's, which only
pushes). -/
theorem table.PairStack.push_spec (p : table.PairStack) (q : Term × Term)
    (h : p.len.val = p.items.val.length) (hmax : p.items.val.length + 1 < Usize.max) :
    table.PairStack.push p q ⦃ p' =>
      p'.items.val = p.items.val ++ [q] ∧ p'.len.val = p'.items.val.length ⦄ := by
  unfold table.PairStack.push
  dsimp only
  split
  · rename_i hlt; simp only [alloc.vec.Vec.len] at hlt; scalar_tac
  step with alloc.vec.Vec.push_spec p.items q (by first | omega | scalar_tac)
    as ⟨v, hv⟩
  step as ⟨i, hi⟩
  refine ⟨hv, ?_⟩
  rw [hv]; simp; scalar_tac

/-! ## The depth of a handle is below it -/

/-- In a store whose terms are well formed, a tail is an earlier handle. -/
theorem StateTail.lt_of_wf {s : Store} (hwf : s.Wf) {t u : Nat} (h : StateTail s.nodes.val t u) :
    u < t := by
  obtain ⟨f, hlt, hd, hl, hu⟩ := h
  have := hwf.wf t hlt
  rw [hd] at this
  have hmem : f.val[1]! ∈ f.val := by
    rw [getElem!_pos f.val 1 (by omega)]; exact List.getElem_mem _
  have := this.1 _ hmem
  simp only [List.length_take] at this
  omega

theorem StateDepth.le_of_wf {s : Store} (hwf : s.Wf) {t d : Nat}
    (h : StateDepth s.nodes.val t d) : d ≤ t := by
  induction h with
  | stop => omega
  | step t u d htl _ ih => have := htl.lt_of_wf hwf; omega

/-! ## The jump a new entry gets -/

theorem jumpOK_tail {nodes : List TermData} {node tail : Term} {base : Nat}
    (ht : StateTail nodes node.val tail.val) (hd : StateDepth nodes tail.val base)
    (b1 : Std.U32) (hb1 : b1.val = base + 1) :
    JumpOK nodes node.val (b1, tail) := by
  intro _
  rw [hb1]
  exact ⟨StateDepth.step _ _ _ ht hd, 1, le_refl _, by omega,
    StateDown.succ _ _ _ _ ht (StateDown.zero _)⟩

/-- The two jumps of the tail: they span at most the tail's depth. -/
theorem jumpOK_two {nodes : List TermData} {jumps : List (Std.U32 × Term)} (hj : JumpsOK nodes jumps)
    {node tail jt jj : Term} {dt dj : Std.U32} {base : Nat}
    (ht : StateTail nodes node.val tail.val) (hd : StateDepth nodes tail.val base)
    (h1 : jumpOf jumps tail.val = some (dt, jt)) (h2 : jumpOf jumps jt.val = some (dj, jj))
    (b1 : Std.U32) (hb1 : b1.val = base + 1) :
    dj.val ≤ dt.val ∧ (jumpDepth jumps jj.val).val ≤ dj.val ∧
      JumpOK nodes node.val (b1, jj) := by
  obtain ⟨_, hdt, k1, hk1, hk1', hdown1⟩ := hj.of_jumpOf h1
  obtain ⟨_, hdj, k2, hk2, hk2', hdown2⟩ := hj.of_jumpOf h2
  dsimp only at hdt hk1' hdown1 hdj hk2' hdown2
  have hdt' := hdt.functional hd
  have hdj' : dj.val = dt.val - k1 := (hdj.functional (hdt.down hdown1 hk1'))
  have hjj := hdj.down hdown2 hk2'
  refine ⟨by omega, ?_, ?_⟩
  · rcases hj.jumpDepth hjj with h | h <;> omega
  · intro _
    rw [hb1]
    refine ⟨StateDepth.step _ _ _ ht hd, 1 + (k1 + k2), by omega, by omega, ?_⟩
    rw [show 1 + (k1 + k2) = (k1 + k2) + 1 by omega]
    exact StateDown.succ _ _ _ _ ht (hdown1.trans hdown2)

/-- The walk's way back up (state_depth_loop0_loop0): each node popped gets its entry, its
depth one more than its tail's and a jump of one tail or of the tail's two
jumps; at the end, the depth of the walk's start. -/
theorem state_up_state_depth_loop0_loop0_spec (h64 : Platform64) (t : Nat) :
    ∀ (pending : table.PairStack) (self : Store) (base : Std.U32) (x : Nat),
      self.Wf → JumpsOK self.nodes.val self.state_jumps.val →
      pending.len.val ≤ pending.items.val.length →
      Chain self.nodes.val t (stk pending) x → StateDepth self.nodes.val x base.val →
      Store.state_depth_loop0_loop0 pending self base ⦃ s' d =>
        (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
        StateDepth s'.nodes.val t d.val ⦄div := by
  apply Store.state_depth_loop0_loop0.fixpoint_induct
    (motive := fun loop => ∀ (pending : table.PairStack) (self : Store) (base : Std.U32) (x : Nat),
      self.Wf → JumpsOK self.nodes.val self.state_jumps.val →
      pending.len.val ≤ pending.items.val.length →
      Chain self.nodes.val t (stk pending) x → StateDepth self.nodes.val x base.val →
      loop pending self base ⦃ s' d =>
        (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
        StateDepth s'.nodes.val t d.val ⦄div)
  · prove_adm
  · intro loop ih pending self base x hwf hj hlen hchain hdepth
    step with table.PairStack.pop_spec pending hlen as ⟨o, pending1, hlen1, ho⟩
    cases o with
    | none =>
      simp only at ho
      rw [ho] at hchain
      have := hchain.nil_eq
      subst this
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨⟨self.state_jumps, rfl⟩, hj, hdepth⟩
    | some q =>
      obtain ⟨node, tail⟩ := q
      simp only at ho ⊢
      rw [ho] at hchain
      obtain ⟨hc1, htl, hx⟩ := hchain.unsnoc
      dsimp only at hc1 htl hx
      subst hx
      have hd1 := StateDepth.step _ _ _ htl hdepth
      have hb1max : base.val + 1 ≤ U32.max := by
        have := hd1.le_of_wf hwf
        have : node.val < 2 ^ 32 := node.hBounds
        scalar_tac
      step as ⟨base1, hbase1⟩
      have hb1 : base1.val = base.val + 1 := by scalar_tac
      have hcont : ∀ jump : Term, JumpOK self.nodes.val node.val (base1, jump) →
          (do
            let self1 ← Store.set_state_jump self node (base1, jump)
            loop pending1 self1 base1) ⦃ s' d =>
            (∃ v, s' = { self with state_jumps := v }) ∧
            JumpsOK s'.nodes.val s'.state_jumps.val ∧ StateDepth s'.nodes.val t d.val ⦄div := by
        intro jump hjump
        step with Store.set_state_jump_spec self node (base1, jump) h64 hj hjump
          as ⟨self1, v, hself1, hv⟩
        subst hself1
        apply WP.dspec_mono (ih pending1 { self with state_jumps := v } base1 node.val ⟨hwf.1, hwf.2, hwf.3⟩ hv hlen1 hc1
          (by rw [hb1]; exact hd1))
        rintro ⟨s', d⟩ ⟨⟨v', hv'⟩, h2, h3⟩
        exact ⟨⟨v', by rw [hv']⟩, h2, h3⟩
      step with Store.state_jump_spec as ⟨o1, ho1⟩
      subst ho1
      cases h1 : jumpOf self.state_jumps.val tail.val with
      | none =>
        simp only [Std.bind_ok]
        exact hcont tail (jumpOK_tail htl hdepth base1 hb1)
      | some e1 =>
        obtain ⟨dt, jt⟩ := e1
        simp only
        step with Store.state_jump_spec as ⟨o2, ho2⟩
        subst ho2
        cases h2 : jumpOf self.state_jumps.val jt.val with
        | none =>
          simp only [Std.bind_ok]
          exact hcont tail (jumpOK_tail htl hdepth base1 hb1)
        | some e2 =>
          obtain ⟨dj, jj⟩ := e2
          simp only
          obtain ⟨hle1, hle2, hjj⟩ := jumpOK_two hj htl hdepth h1 h2 base1 hb1
          step with Store.state_jump_depth_spec as ⟨djj, hdjj⟩
          subst hdjj
          step as ⟨i, hi⟩
          step as ⟨i1, hi1⟩
          split
          · simp only [Std.bind_ok]; exact hcont jj hjj
          · simp only [Std.bind_ok]; exact hcont tail (jumpOK_tail htl hdepth base1 hb1)

/-- The walk's way back up (state_depth_loop0_loop1): each node popped gets its entry, its
depth one more than its tail's and a jump of one tail or of the tail's two
jumps; at the end, the depth of the walk's start. -/
theorem state_up_state_depth_loop0_loop1_spec (h64 : Platform64) (t : Nat) :
    ∀ (pending : table.PairStack) (self : Store) (base : Std.U32) (x : Nat),
      self.Wf → JumpsOK self.nodes.val self.state_jumps.val →
      pending.len.val ≤ pending.items.val.length →
      Chain self.nodes.val t (stk pending) x → StateDepth self.nodes.val x base.val →
      Store.state_depth_loop0_loop1 pending self base ⦃ s' d =>
        (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
        StateDepth s'.nodes.val t d.val ⦄div := by
  apply Store.state_depth_loop0_loop1.fixpoint_induct
    (motive := fun loop => ∀ (pending : table.PairStack) (self : Store) (base : Std.U32) (x : Nat),
      self.Wf → JumpsOK self.nodes.val self.state_jumps.val →
      pending.len.val ≤ pending.items.val.length →
      Chain self.nodes.val t (stk pending) x → StateDepth self.nodes.val x base.val →
      loop pending self base ⦃ s' d =>
        (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
        StateDepth s'.nodes.val t d.val ⦄div)
  · prove_adm
  · intro loop ih pending self base x hwf hj hlen hchain hdepth
    step with table.PairStack.pop_spec pending hlen as ⟨o, pending1, hlen1, ho⟩
    cases o with
    | none =>
      simp only at ho
      rw [ho] at hchain
      have := hchain.nil_eq
      subst this
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨⟨self.state_jumps, rfl⟩, hj, hdepth⟩
    | some q =>
      obtain ⟨node, tail⟩ := q
      simp only at ho ⊢
      rw [ho] at hchain
      obtain ⟨hc1, htl, hx⟩ := hchain.unsnoc
      dsimp only at hc1 htl hx
      subst hx
      have hd1 := StateDepth.step _ _ _ htl hdepth
      have hb1max : base.val + 1 ≤ U32.max := by
        have := hd1.le_of_wf hwf
        have : node.val < 2 ^ 32 := node.hBounds
        scalar_tac
      step as ⟨base1, hbase1⟩
      have hb1 : base1.val = base.val + 1 := by scalar_tac
      have hcont : ∀ jump : Term, JumpOK self.nodes.val node.val (base1, jump) →
          (do
            let self1 ← Store.set_state_jump self node (base1, jump)
            loop pending1 self1 base1) ⦃ s' d =>
            (∃ v, s' = { self with state_jumps := v }) ∧
            JumpsOK s'.nodes.val s'.state_jumps.val ∧ StateDepth s'.nodes.val t d.val ⦄div := by
        intro jump hjump
        step with Store.set_state_jump_spec self node (base1, jump) h64 hj hjump
          as ⟨self1, v, hself1, hv⟩
        subst hself1
        apply WP.dspec_mono (ih pending1 { self with state_jumps := v } base1 node.val ⟨hwf.1, hwf.2, hwf.3⟩ hv hlen1 hc1
          (by rw [hb1]; exact hd1))
        rintro ⟨s', d⟩ ⟨⟨v', hv'⟩, h2, h3⟩
        exact ⟨⟨v', by rw [hv']⟩, h2, h3⟩
      step with Store.state_jump_spec as ⟨o1, ho1⟩
      subst ho1
      cases h1 : jumpOf self.state_jumps.val tail.val with
      | none =>
        simp only [Std.bind_ok]
        exact hcont tail (jumpOK_tail htl hdepth base1 hb1)
      | some e1 =>
        obtain ⟨dt, jt⟩ := e1
        simp only
        step with Store.state_jump_spec as ⟨o2, ho2⟩
        subst ho2
        cases h2 : jumpOf self.state_jumps.val jt.val with
        | none =>
          simp only [Std.bind_ok]
          exact hcont tail (jumpOK_tail htl hdepth base1 hb1)
        | some e2 =>
          obtain ⟨dj, jj⟩ := e2
          simp only
          obtain ⟨hle1, hle2, hjj⟩ := jumpOK_two hj htl hdepth h1 h2 base1 hb1
          step with Store.state_jump_depth_spec as ⟨djj, hdjj⟩
          subst hdjj
          step as ⟨i, hi⟩
          step as ⟨i1, hi1⟩
          split
          · simp only [Std.bind_ok]; exact hcont jj hjj
          · simp only [Std.bind_ok]; exact hcont tail (jumpOK_tail htl hdepth base1 hb1)

/-- The walk down from `t` (to a node with an entry, or to the end of the
list), then back up: the depth of `t`, and only entries that are right. -/
theorem state_down_spec (h64 : Platform64) (self : Store) (hinv : self.Inv) (t : Nat)
    (ht : t < 2 ^ 32) :
    ∀ (x : Term) (pending : table.PairStack),
      pending.len.val = pending.items.val.length →
      Chain self.nodes.val t pending.items.val x.val →
      pending.items.val.length + x.val ≤ t →
      Store.state_depth_loop0 x self stateCons pending ⦃ r s' =>
        (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
        match r with
        | core.result.Result.Ok d => StateDepth s'.nodes.val t d.val
        | core.result.Result.Err _ => True ⦄div := by
  have hstk : ∀ p : table.PairStack, p.len.val = p.items.val.length → stk p = p.items.val := by
    intro p h; unfold stk; rw [h, List.take_length]
  apply Store.state_depth_loop0.fixpoint_induct self stateCons
    (motive := fun loop => ∀ (x : Term) (pending : table.PairStack),
      pending.len.val = pending.items.val.length →
      Chain self.nodes.val t pending.items.val x.val →
      pending.items.val.length + x.val ≤ t →
      loop x pending ⦃ r s' =>
        (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
        match r with
        | core.result.Result.Ok d => StateDepth s'.nodes.val t d.val
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih x pending hlen hchain hbound
    have hup : ∀ (base : Std.U32), StateDepth self.nodes.val x.val base.val →
        ∀ (upl : table.PairStack → Store → Std.U32 → Result (Store × Std.U32)),
        (upl pending self base ⦃ s' d =>
          (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
          StateDepth s'.nodes.val t d.val ⦄div) →
        (do
          let (self1, base) ← upl pending self base
          ok ((core.result.Result.Ok base : core.result.Result Std.U32 CheckError), self1)) ⦃ r s' =>
          (∃ v, s' = { self with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
          match r with
          | core.result.Result.Ok d => StateDepth s'.nodes.val t d.val
          | core.result.Result.Err _ => True ⦄div := by
      intro base _ upl hupl
      apply WP.dspec_bind hupl
      rintro ⟨s', d⟩ h
      first
        | exact h
        | simpa using h
        | (simp only [WP.uncurry'_pair] at h; simp only [WP.dspec_ok]; exact h)
    step with Store.state_jump_spec as ⟨o, ho⟩
    subst ho
    cases h1 : jumpOf self.state_jumps.val x.val with
    | some e =>
      obtain ⟨d, j⟩ := e
      simp only
      obtain ⟨_, hd, _⟩ := hinv.jumps.of_jumpOf h1
      exact hup d hd _ (state_up_state_depth_loop0_loop1_spec h64 t pending self d x.val hinv.terms
        hinv.jumps (by omega) (by rw [hstk _ hlen]; exact hchain) hd)
    | none =>
      simp only
      step with Store.state_tail_spec self hinv x as ⟨r, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        first
          | exact ⟨⟨self.state_jumps, rfl⟩, hinv.jumps⟩
          | exact ⟨⟨self.state_jumps, rfl⟩, hinv.jumps, trivial⟩
          | exact hinv.jumps
      | Ok o =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        cases o with
        | none =>
          simp only at hr ⊢
          obtain ⟨hlt, hno⟩ := hr
          have hd : StateDepth self.nodes.val x.val (0#u32 : Std.U32).val :=
            StateDepth.stop _ hlt hno
          exact hup 0#u32 hd _ (state_up_state_depth_loop0_loop0_spec h64 t pending self 0#u32 x.val
            hinv.terms hinv.jumps (by omega) (by rw [hstk _ hlen]; exact hchain) hd)
        | some tail =>
          simp only at hr ⊢
          obtain ⟨htl, hlt⟩ := hr
          have hmax : (2 : Nat) ^ 40 ≤ Usize.max := h64
          have htail := tail.hBounds
          step with table.PairStack.push_spec pending (x, tail) hlen (by omega)
            as ⟨pending1, hp1, hl1⟩
          apply ih tail pending1 hl1 (by rw [hp1]; exact Chain.snoc _ _ _ _ hchain htl)
          rw [hp1]; simp; omega

/-- The search for the node at depth `target` below `t` (of depth `D`):
where it answers, the node `D - target` tails down. -/
theorem state_ancestor_spec (self : Store) (hinv : self.Inv) (target : Std.U32) (t D : Nat) :
    ∀ x : Term, (∃ k dx, StateDown self.nodes.val t k x.val ∧ StateDepth self.nodes.val x.val dx ∧
        k + dx = D ∧ target.val ≤ dx) →
      Store.state_ancestor_loop x self stateCons target ⦃ r =>
        match r with
        | core.result.Result.Ok y => StateDown self.nodes.val t (D - target.val) y.val
        | core.result.Result.Err _ => True ⦄div := by
  apply Store.state_ancestor_loop.fixpoint_induct self stateCons target
    (motive := fun loop => ∀ x : Term, (∃ k dx, StateDown self.nodes.val t k x.val ∧
        StateDepth self.nodes.val x.val dx ∧ k + dx = D ∧ target.val ≤ dx) →
      loop x ⦃ r =>
        match r with
        | core.result.Result.Ok y => StateDown self.nodes.val t (D - target.val) y.val
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih x ⟨k, dx, hk, hdx, hsum, hle⟩
    step with Store.state_jump_spec as ⟨o, ho⟩
    subst ho
    cases h1 : jumpOf self.state_jumps.val x.val with
    | none => simp
    | some e =>
      obtain ⟨d, jump⟩ := e
      obtain ⟨hpos, hd, k', hk1, hk2, hdown⟩ := hinv.jumps.of_jumpOf h1
      dsimp only at hpos hd hk2 hdown
      have hdd : d.val = dx := hd.functional hdx
      show (if d = target then _ else _) ⦃ _ ⦄div
      split
      · rename_i heq
        simp only [WP.dspec_ok]
        have : D - target.val = k := by rw [← heq]; omega
        rw [this]; exact hk
      · rename_i hne
        have hne' : d.val ≠ target.val := fun h => hne (by scalar_tac)
        step with Store.state_jump_depth_spec as ⟨dj, hdj⟩
        subst hdj
        have hjd := hd.down hdown hk2
        split
        · rename_i hge
          apply ih jump ⟨k + k', d.val - k', hk.trans hdown, hjd, by omega, ?_⟩
          rcases hinv.jumps.jumpDepth hjd with h | h
          · have : target.val ≤ 0 := by rw [← h]; scalar_tac
            omega
          · rw [← h]; scalar_tac
        · step with Store.state_tail_spec self hinv x as ⟨r, hr⟩
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok o =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
            cases o with
            | none => simp
            | some tail =>
              simp only at hr ⊢
              obtain ⟨htl, _⟩ := hr
              have hdt : StateDepth self.nodes.val tail.val (d.val - 1) := by
                have := hd.down (StateDown.succ _ _ _ _ htl (StateDown.zero _)) (by omega)
                exact this
              apply ih tail ⟨k + 1, d.val - 1,
                hk.trans (StateDown.succ _ _ _ _ htl (StateDown.zero _)), hdt, by omega, by omega⟩

theorem UScalar.saturating_add_val {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.saturating_add x y).val = min (UScalar.max ty) (x.val + y.val) := by
  unfold UScalar.saturating_add
  show (BitVec.ofNat ty.numBits _).toNat = _
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h := UScalar.max_def ty
  have hp : 0 < 2 ^ ty.numBits := Nat.pos_of_ne_zero (by simp)
  omega

/-- `charge` counts calls: nothing else of the store changes, and the
budget goes down. It stores the saturating sum that it tested, which is at
least the calls counted before. -/
theorem Store.charge_spec (s : Store) (count : Std.U64) :
    Store.charge s count ⦃ r s' => (∃ c, s' = { s with calls := c }) ∧ s'.budget ≤ s.budget ⦄ := by
  unfold Store.charge
  step as ⟨sum, hsum⟩
  have hge : s.calls.val ≤ sum.val := by
    rw [hsum]
    show s.calls.val ≤ (UScalar.saturating_add s.calls count).val
    rw [UScalar.saturating_add_val]
    have h1 := s.calls.hmax
    have h2 := UScalar.max_def UScalarTy.U64
    omega
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    refine ⟨⟨_, rfl⟩, ?_⟩
    simp [Store.budget]
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    refine ⟨⟨_, rfl⟩, ?_⟩
    simp only [Store.budget]; omega

theorem Store.Inv.with_jumps {s : Store} (h : s.Inv) (v : alloc.vec.Vec (Std.U32 × Term))
    (hv : JumpsOK s.nodes.val v.val) : ({ s with state_jumps := v } : Store).Inv := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4⟩, _⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4⟩, hv⟩

theorem Store.Inv.with_calls {s : Store} (h : s.Inv) (c : Std.U64) :
    ({ s with calls := c } : Store).Inv := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4⟩, d⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3, c4⟩, d⟩

theorem Store.state_depth_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) (t : Term) :
    Store.state_depth s stateCons t ⦃ r s' =>
      (∃ v, s' = { s with state_jumps := v }) ∧ JumpsOK s'.nodes.val s'.state_jumps.val ∧
      match r with
      | core.result.Result.Ok d => StateDepth s'.nodes.val t.val d.val
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.state_depth
  step with table.PairStack.new_spec as ⟨p, hp0, hp1⟩
  exact state_down_spec h64 s hinv t.val t.hBounds t p (by rw [hp0, hp1]; rfl)
    (by rw [hp1]; exact Chain.nil _) (by rw [hp1]; simp)

/-- A handle of a native integer is a native numeral. -/
theorem Rep.int_data {nodes : List TermData} {t : Nat} {n : Int} (h : Rep nodes t n) :
    t < nodes.length ∧ nodes[t]! = TermData.Native (lit.Lit.Numeral (num.Integer.ofInt n)) := by
  obtain ⟨hh, _⟩ := h
  change Holds nodes t (Tree.encInt n) at hh
  simp only [Tree.encInt] at hh
  cases hh with
  | native _ _ hlt hd => exact ⟨hlt, hd⟩

/-- What `state_nth` is proved to give, from a store `s0`: an object of the
state's, the literal `true`, or an error. -/
def NthPost (s0 : Store) (S : Eo.CState) (n : Int)
    (r : core.result.Result (Option Term) CheckError) (s' : Store) : Prop :=
  s'.Inv ∧ s0.Grows s' ∧
    match r with
    | core.result.Result.Ok none => Eo.__eo_state_proven_nth S n = Eo.Term.Boolean true
    | core.result.Result.Ok (some e) => ∃ so, Represents.rep s' e so ∧
        Eo.__eo_state_proven_nth S n = Eo.__eo_StateObj_proven so
    | core.result.Result.Err _ => True

/-- `charge`, then the rest `K` where it succeeds and its error where not. -/
theorem charge_then (s0 s : Store) (hinv : s.Inv) (hG : s0.Grows s) (S : Eo.CState) (n : Int)
    (count : Std.U64)
    (K : Store → Result ((core.result.Result (Option Term) CheckError) × Store))
    (hK : ∀ c : Std.U64, ({ s with calls := c } : Store).Inv → s0.Grows { s with calls := c } →
      K { s with calls := c } ⦃ r s' => NthPost s0 S n r s' ⦄div) :
    (do
      let (r2, self2) ← Store.charge s count
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ => K self2
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (Option Term) (core.convert.FromSame CheckError) residual
        ok (r3, self2)) ⦃ r s' => NthPost s0 S n r s' ⦄div := by
  step with Store.charge_spec s count as ⟨r2, s2, c, hc, hb⟩
  subst hc
  have hinv2 := hinv.with_calls c
  have hG2 : s0.Grows { s with calls := c } := hG.trans ⟨List.prefix_refl _, rfl, rfl, hb⟩
  cases r2 with
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    exact hK c hinv2 hG2
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv2, hG2, trivial⟩

/-- The index as `state_nth` reads it, then the rest `K`: `some (some k)`
for `k` in `u32`, `some none` for a negative or larger numeral. -/
theorem index_then (s0 : Store) (S : Eo.CState) (n : Int)
    (K : Option (Option Std.U64) → Result ((core.result.Result (Option Term) CheckError) × Store))
    (h1 : ∀ k : Std.U64, (k.val : Int) = n → 0 ≤ n → n < 2 ^ 32 →
      K (some (some k)) ⦃ r s' => NthPost s0 S n r s' ⦄div)
    (h2 : n < 0 ∨ 2 ^ 32 ≤ n → K (some none) ⦃ r s' => NthPost s0 S n r s' ⦄div) :
    (do
      let m ← (do
        let i ← num.Integer.sgn (num.Integer.ofInt n)
        let o ←
          if i >= 0#i32
          then do
            let b ← num.Integer.fits_u32 (num.Integer.ofInt n)
            if b = true
            then do
              let i1 ← num.Integer.to_u32 (num.Integer.ofInt n)
              let i2 ← lift (core.convert.num.FromU64U32.from i1)
              ok (some i2)
            else ok none
          else ok none
        ok (some o))
      K m) ⦃ r s' => NthPost s0 S n r s' ⦄div := by
  obtain ⟨r, hr, hrv⟩ := num.Integer.sgn_spec (num.Integer.ofInt n)
  rw [num.Integer.toInt_ofInt] at hrv
  rw [hr]
  simp only [Std.bind_ok]
  split
  · rename_i hge
    have hn0 : 0 ≤ n := by
      have : (0 : Int) ≤ r.val := by scalar_tac
      rw [hrv] at this
      rcases Int.lt_trichotomy n 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h] at this; omega
      · omega
      · omega
    rw [num.Integer.fits_u32_spec, num.Integer.toInt_ofInt]
    simp only [Std.bind_ok]
    split
    · rename_i hb
      simp only [decide_eq_true_eq] at hb
      obtain ⟨u, hu, huv⟩ := num.Integer.to_u32_spec (num.Integer.ofInt n)
      rw [num.Integer.toInt_ofInt, if_pos hb] at huv
      rw [hu]
      simp only [Std.bind_ok, lift]
      apply h1 _ ?_ hb.1 hb.2
      rw [← huv]
      first | rfl | simp | (simp [core.convert.num.FromU64U32.from]; done) | scalar_tac
    · rename_i hb
      simp only [decide_eq_true_eq, not_and, not_lt] at hb
      simp only [Std.bind_ok]
      exact h2 (Or.inr (hb hn0))
  · rename_i hlt
    simp only [Std.bind_ok]
    apply h2; left
    have : r.val < 0 := by scalar_tac
    rw [hrv] at this
    rcases Int.lt_trichotomy n 0 with h | h | h
    · exact h
    · subst h; simp at this
    · rw [Int.sign_eq_one_of_pos h] at this; omega

/-- **`state_nth` finds what logos's `__eo_state_proven_nth` looks up**: for
handles of a state `S` and an index `n`, the handle of the `n`-th object of
`S`, of which the program gives `__eo_StateObj_proven`; `none` where logos
gives `true`; or an error. -/
theorem Store.state_nth_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) (state index : Term)
    (S : Eo.CState) (n : Int) (hS : Represents.rep s state S) (hn : Represents.rep s index n) :
    Store.state_nth s stateCons state index ⦃ r s' => NthPost s S n r s' ⦄div := by
  unfold Store.state_nth
  step with Store.state_depth_spec s hinv h64 state as ⟨r, s1, v, hv, hj1, hr⟩
  subst hv
  have hinv1 : ({ s with state_jumps := v } : Store).Inv := hinv.with_jumps v hj1
  have hG1 : s.Grows { s with state_jumps := v } := ⟨List.prefix_refl _, rfl, rfl, le_refl _⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv1, hG1, trivial⟩
  | Ok D =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr ⊢
    have hlen : D.val = stateLen S := Rep.state_depth hS hr
    have hD32 : D.val < 2 ^ 32 := by
      have := hr.le_of_wf hinv.terms
      have : state.val < 2 ^ 32 := by scalar_tac
      omega
    split
    · rename_i hD0
      apply charge_then s _ hinv1 hG1 S n 1#u64
      intro c hinv2 hG2
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv2, hG2, ?_⟩
      have : stateLen S = 0 := by rw [← hlen, hD0]; rfl
      apply state_proven_nth_out
      omega
    · rename_i hD0
      have hDpos : 0 < D.val := by
        have : D.val ≠ 0 := fun h => hD0 (by scalar_tac)
        omega
      obtain ⟨hilt, hidata⟩ := Rep.int_data hn
      rw [Store.view_eq]
      have hilt' : index.val < (({ s with state_jumps := v } : Store)).nodes.length := hilt
      simp only [hilt', ite_true, Std.bind_ok]
      have hidata' : (({ s with state_jumps := v } : Store)).nodes.val[index.val]! =
          TermData.Native (lit.Lit.Numeral (num.Integer.ofInt n)) := hidata
      rw [hidata']
      simp only
      apply index_then s S n
      · intro k hkn hn0 hn32
        simp only
        step as ⟨iD, hiD⟩
        split
        · rename_i hkD
          have hkD' : k.val < D.val := by scalar_tac
          step as ⟨i1, hi1⟩
          apply charge_then s _ hinv1 hG1 S n _
          intro c hinv2 hG2
          step as ⟨k32, hk32⟩
          have hk32v : k32.val = k.val := by scalar_tac
          step as ⟨tgt, htgt⟩
          have htgtv : tgt.val = D.val - k.val := by scalar_tac
          step with state_ancestor_spec { s with state_jumps := v, calls := c } hinv2 tgt state.val
            D.val state ⟨0, D.val, StateDown.zero _, hr, by omega, by omega⟩ as ⟨r3, hr3⟩
          cases r3 with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            exact ⟨hinv2, hG2, trivial⟩
          | Ok y =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr3 ⊢
            have hky : D.val - tgt.val = k.val := by omega
            rw [hky] at hr3
            have hyrep := Rep.state_down hS hr3
            have hyd : StateDepth s.nodes.val y.val (D.val - k.val) := hr.down hr3 (by omega)
            obtain ⟨u, htl⟩ : ∃ u, StateTail s.nodes.val y.val u := by
              generalize hdk : D.val - k.val = dk at hyd
              cases hyd with
              | stop _ _ _ => omega
              | step _ u d' htl hd' => exact ⟨u, htl⟩
            cases hdrop : stateDrop S k.val with
            | cons so S' =>
              rw [hdrop] at hyrep
              obtain ⟨fv, a, b, hylt, hyd', hfv, ha, _⟩ := hyrep.state_cons
              rw [Store.view_eq]
              have hylt' : y.val < (({ s with state_jumps := v, calls := c } : Store)).nodes.length :=
                hylt
              simp only [hylt', ite_true, Std.bind_ok]
              have hyd'' : (({ s with state_jumps := v, calls := c } : Store)).nodes.val[y.val]! =
                  TermData.Node stateCons fv := hyd'
              rw [hyd'']
              simp only
              step with alloc.vec.Vec.index_usize_spec fv 0#usize (by simp [hfv])
                as ⟨e0, he0⟩
              simp only [WP.dspec_ok, WP.uncurry'_pair]
              refine ⟨hinv2, hG2, so, ?_, ?_⟩
              · have : e0 = a := by rw [he0]; simp [hfv]
                rw [this]; exact ha
              · have : n = (k.val : Int) := by omega
                rw [this]; exact state_proven_nth_drop S k.val so S' hdrop
            | _ =>
              rw [hdrop] at hyrep
              exact absurd htl (hyrep.state_not_cons (by intro _ _ h; cases h) u)
        · rename_i hkD
          have hkD' : D.val ≤ k.val := by scalar_tac
          step as ⟨i1, hi1⟩
          step as ⟨i2, hi2⟩
          apply charge_then s _ hinv1 hG1 S n _
          intro c hinv2 hG2
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv2, hG2, ?_⟩
          apply state_proven_nth_out
          omega
      · intro hout
        simp only
        step as ⟨i1, hi1⟩
        step as ⟨i2, hi2⟩
        apply charge_then s _ hinv1 hG1 S n _
        intro c hinv2 hG2
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv2, hG2, ?_⟩
        apply state_proven_nth_out
        omega

end pathos_compiled_checker
