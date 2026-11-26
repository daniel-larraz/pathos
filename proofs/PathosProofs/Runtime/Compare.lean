module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Trusted
public import PathosProofs.Store.Tree
public import PathosProofs.Store.Ops

/-!
# `eo::cmp`: the runtime's `Store::compare`, against a total order on trees

`Store::compare` (the compiled checker's `src/lib.rs`) orders two terms without recursion: it
keeps a stack of pairs still to compare, pops one, and either decides the
order (different keys or literals) or pushes the pairs of their children.
Here: `treeCmp`, the order it computes on the trees the handles stand for
(`Holds`), and `compare_spec`, that `compare` returns it. The stack cannot
overflow: what it holds is blocks of at most `A` pairs (the largest arity)
whose bounds strictly decrease (`Blocks`), so at most `A * (M + 1)` pairs
for `M` terms.

The order of constructors (`order_key`) and their arities are hypotheses
here; the checker's are discharged per constructor, by generated lemmas.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- Lexicographic order on lists of numbers: logos's `stringCmp`, and
`code_points_cmp` on code points. -/
def lexNat : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x = y then lexNat xs ys else compare x y

theorem lexNat_nil_left (ys : List Nat) : lexNat [] ys = compare 0 ys.length := by
  cases ys <;> simp [lexNat, compare, compareOfLessAndEq]

theorem lexNat_nil_right (xs : List Nat) (h : xs ≠ []) : lexNat xs [] = .gt := by
  cases xs <;> simp_all [lexNat]

theorem code_points_cmp_loop_spec (a b : Slice Std.U32) :
    ∀ (k : Nat) (i : Std.Usize), a.length - i.val = k → i.val ≤ a.length → i.val ≤ b.length →
      code_points_cmp_loop a b Ordering.eq i true ⦃ r =>
        r = lexNat ((a.val.drop i.val).map (·.val)) ((b.val.drop i.val).map (·.val)) ⦄div := by
  intro k
  induction k with
  | zero =>
    intro i hk ha hb
    have heq : i = Slice.len a := by
      apply UScalar.eq_of_val_eq; scalar_tac
    subst heq
    unfold code_points_cmp_loop
    simp only [ite_true, lift, Std.bind_ok]
    unfold code_points_cmp_loop
    simp only [Bool.false_eq_true, ite_false, WP.dspec_ok]
    have hd : a.val.drop (Slice.len a).val = [] :=
      List.drop_eq_nil_of_le (by simp [Slice.len])
    rw [hd, List.map_nil, lexNat_nil_left]
    show compare (Slice.len a).val (Slice.len b).val = _
    have hla : (Slice.len a).val = a.val.length := by scalar_tac
    have hlb : (Slice.len b).val = b.val.length := by scalar_tac
    rw [hla, hlb, List.length_map, List.length_drop]
    by_cases h : a.val.length = b.val.length
    · rw [h]; simp
    · have hlt : a.val.length < b.val.length := by scalar_tac
      have hpos : 0 < b.val.length - a.val.length := by omega
      simp only [compare, compareOfLessAndEq, hlt, hpos, ite_true]
  | succ k ih =>
    intro i hk ha hb
    have hlt : i.val < a.val.length := by scalar_tac
    have hne : ¬ (i = Slice.len a) := by
      intro h; have := congrArg UScalar.val h; scalar_tac
    unfold code_points_cmp_loop
    simp only [ite_true, hne, ite_false]
    by_cases hib : i = Slice.len b
    · simp only [hib, ite_true, lift, Std.bind_ok]
      unfold code_points_cmp_loop
      simp only [Bool.false_eq_true, ite_false, WP.dspec_ok]
      have hlb : (Slice.len b).val = b.val.length := by scalar_tac
      have hla : (Slice.len a).val = a.val.length := by scalar_tac
      have hi : i.val = b.val.length := by rw [hib]; exact hlb
      have hdb : b.val.drop i.val = [] := List.drop_eq_nil_of_le (by omega)
      rw [← hib, hdb, List.map_nil, lexNat_nil_right _ (by simp; omega)]
      show compare (Slice.len a).val i.val = _
      rw [hla, hi]
      have : b.val.length < a.val.length := by omega
      simp [compare, compareOfLessAndEq, Nat.lt_asymm this, Nat.ne_of_gt this]
    · simp only [hib, ite_false]
      have hltb : i.val < b.val.length := by
        have : i.val ≠ b.val.length := fun h => hib (UScalar.eq_of_val_eq (by scalar_tac))
        scalar_tac
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hda : a.val.drop i.val = x :: a.val.drop (i.val + 1) := by
        rw [hx]; exact List.drop_eq_getElem_cons hlt
      have hdb : b.val.drop i.val = y :: b.val.drop (i.val + 1) := by
        rw [hy]; exact List.drop_eq_getElem_cons hltb
      rw [hda, hdb]
      split
      · rename_i hxy
        simp only [lift, Std.bind_ok]
        unfold code_points_cmp_loop
        simp only [Bool.false_eq_true, ite_false, WP.dspec_ok]
        have hv : x.val ≠ y.val := fun h => by simp_all [UScalar.eq_of_val_eq h]
        simp [lexNat, hv]
      · rename_i hxy
        have hv : x.val = y.val := by simp_all
        step as ⟨i5, hi5⟩
        apply WP.dspec_mono (ih i5 (by scalar_tac) (by scalar_tac) (by scalar_tac))
        intro r hr
        rw [hr, show i5.val = i.val + 1 by scalar_tac]
        simp [lexNat, hv]

theorem code_points_cmp_spec (a b : Slice Std.U32) :
    code_points_cmp a b ⦃ r => r = lexNat (a.val.map (·.val)) (b.val.map (·.val)) ⦄div := by
  unfold code_points_cmp
  apply WP.dspec_mono (code_points_cmp_loop_spec a b _ 0#usize rfl (by simp) (by simp))
  intro r hr; simpa using hr

theorem integer_cmp_eq (a b : num.Integer) : integer_cmp a b = ok (compare a.toInt b.toInt) := by
  unfold integer_cmp
  simp [num.Integer.partial_cmp_spec, core.option.Option.unwrap_or]

/-- What `literal_cmp` gives, where it gives an order: by value for numerals,
by numerator and then denominator for rationals, by width and then value for
binaries, by code points for strings. The other pairs are errors (`.eq`
here, which no result is compared with). -/
noncomputable def litCmp : lit.Lit → lit.Lit → Ordering
  | .Boolean a, .Boolean b => if a = b then .eq else if b then .lt else .gt
  | .Numeral a, .Numeral b => compare a.toInt b.toInt
  | .Rational a, .Rational b =>
    (compare a.toRat.num b.toRat.num).then (compare (a.toRat.den : Int) (b.toRat.den : Int))
  | .Binary a, .Binary b => (compare a.size.val b.size.val).then (compare a.value.toInt b.value.toInt)
  | .Str a, .Str b => lexNat (a.val.map (·.val)) (b.val.map (·.val))
  | _, _ => .eq

theorem literal_cmp_spec (a b : lit.Lit) :
    literal_cmp a b ⦃ r => ∀ o, r = core.result.Result.Ok o → o = litCmp a b ⦄div := by
  unfold literal_cmp
  cases a <;> cases b <;> simp only [WP.dspec_ok, litCmp] <;> (try (intro o h; cases h))
  case Boolean.Boolean x y =>
    split
    · simp_all
    · split <;> simp_all
  case Numeral.Numeral x y =>
    simp only [integer_cmp_eq, Std.bind_ok, WP.dspec_ok]
    intro o h; cases h; rfl
  case Rational.Rational x y =>
    simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, integer_cmp_eq,
      num.Integer.toInt_ofInt, Std.bind_ok]
    split <;> rename_i hc <;> simp only [WP.dspec_ok] <;> intro o h <;> cases h <;>
      simp [Ordering.then, hc]
  case Binary.Binary x y =>
    simp only [bitvec.BitVec.impl.size, bitvec.BitVec.impl.value, integer_cmp_eq, lift,
      Std.bind_ok]
    split <;> rename_i hc <;> simp only [WP.dspec_ok] <;> intro o h <;> cases h <;>
      simp_all [Ordering.then]
  case Str.Str x y =>
    simp only [eostring.EoString.code_points, Std.bind_ok]
    apply WP.dspec_bind (code_points_cmp_spec _ _)
    intro r hr
    simp only [WP.dspec_ok]
    intro o h; cases h
    rw [hr]; simp [alloc.vec.Vec.deref]


/-! ## The order on the store's trees -/

/-- The data a tree's root is stored as, but for the fields: what
`Store.order_key` looks at. -/
def Tree.shape : Tree → TermData
  | .stuck => .Stuck
  | .lit l => .Literal l
  | .native l => .Native l
  | .userop c => .UserOp c
  | .apply _ _ => .Apply 0#u32 0#u32
  | .node c _ => .Node c (alloc.vec.Vec.new Term)

/-- The key `Store.order_key` gives a tree's root is `treeKey`'s, given that
the calculus's tables give keys (`hok`, `hemb`). -/
theorem treeKey_of (hok : ∀ c, ∃ p, schema.Constructor.order_key c = ok p)
    (hemb : ∀ e, ∃ o, schema.Constructor.of_embedding e = ok o)
    {t : Tree} {p : Std.Usize × Std.Usize}
    (h : Store.order_key t.shape = ok (core.result.Result.Ok p)) :
    treeKey t = some (p.1.val, p.2.val) := by
  have hE : ∀ e, (do
      let o ← schema.Constructor.of_embedding e
      match o with
      | none => ok (core.result.Result.Err CheckError.InvalidConstructor)
      | some c => do
        let p ← schema.Constructor.order_key c
        ok (core.result.Result.Ok p) : Result _) = ok (core.result.Result.Ok p) →
      embKey e = some (p.1.val, p.2.val) := by
    intro e he
    obtain ⟨o, ho⟩ := hemb e
    rw [ho, Std.bind_ok] at he
    cases o with
    | none => have := Result.ok_injective he; cases this
    | some c =>
      obtain ⟨q, hq⟩ := hok c
      simp only [hq, Std.bind_ok] at he
      have := Result.ok_injective he; cases this
      exact embKey_of ho hq
  cases t with
  | stuck => exact hE _ h
  | lit l =>
    cases l <;> (simp only [Tree.shape, Store.order_key, Std.bind_ok] at h; exact hE _ h)
  | native l =>
    simp only [Tree.shape, Store.order_key] at h
    have := Result.ok_injective h; cases this; rfl
  | userop c =>
    obtain ⟨q, hq⟩ := hok c
    simp only [Tree.shape, Store.order_key, hq, Std.bind_ok] at h
    have := Result.ok_injective h; cases this
    exact ctorKey_of hq
  | apply a b => exact hE _ h
  | node c xs =>
    obtain ⟨q, hq⟩ := hok c
    simp only [Tree.shape, Store.order_key, hq, Std.bind_ok] at h
    have := Result.ok_injective h; cases this
    exact ctorKey_of hq

mutual
/-- The order `Store.compare` computes on the trees two handles unfold to:
the roots' keys, then a literal's value, or the fields from left to right.
Where the runtime gives an error (no key, two shapes it does not compare),
`.eq`, which no result is compared with. -/
noncomputable def treeCmp : Tree → Tree → Ordering
  | x, y =>
    match treeKey x, treeKey y with
    | some kx, some ky =>
      match (compare kx.1 ky.1).then (compare kx.2 ky.2) with
      | .eq => bodyCmp x y
      | o => o
    | _, _ => .eq
noncomputable def bodyCmp : Tree → Tree → Ordering
  | .lit l, .lit m => litCmp l m
  | .native l, .native m => litCmp l m
  | .apply f a, .apply g b => (treeCmp f g).then (treeCmp a b)
  | .node _ xs, .node _ ys => if xs.length = ys.length then listCmp xs ys else .eq
  | _, _ => .eq
noncomputable def listCmp : List Tree → List Tree → Ordering
  | x :: xs, y :: ys => (treeCmp x y).then (listCmp xs ys)
  | _, _ => .eq
end


theorem litCmp_refl (l : lit.Lit) : litCmp l l = .eq := by
  cases l <;> simp [litCmp, Ordering.then, compare, compareOfLessAndEq]
  rename_i x
  -- strings: lexNat is reflexive
  induction (x.val.map (·.val)) with
  | nil => simp [lexNat]
  | cons c cs ih => simp [lexNat, ih]

mutual
theorem treeCmp_refl : ∀ t : Tree, treeCmp t t = .eq
  | t => by
    unfold treeCmp
    split
    · rename_i kx ky hx hy
      rw [hx] at hy; cases hy
      have h1 : compare kx.1 kx.1 = .eq := by simp [compare, compareOfLessAndEq]
      have h2 : compare kx.2 kx.2 = .eq := by simp [compare, compareOfLessAndEq]
      simp only [h1, h2]
      exact bodyCmp_refl _
    · rfl
theorem bodyCmp_refl : ∀ t : Tree, bodyCmp t t = .eq
  | .stuck => by simp [bodyCmp]
  | .lit l => by simp [bodyCmp, litCmp_refl]
  | .native l => by simp [bodyCmp, litCmp_refl]
  | .userop c => by simp [bodyCmp]
  | .apply f a => by simp [bodyCmp, treeCmp_refl f, treeCmp_refl a, Ordering.then]
  | .node c xs => by simp [bodyCmp, listCmp_refl xs]
theorem listCmp_refl : ∀ xs : List Tree, listCmp xs xs = .eq
  | [] => by simp [listCmp]
  | x :: xs => by simp [listCmp, treeCmp_refl x, listCmp_refl xs, Ordering.then]
end


/-! ## The stack of pairs -/

/-- The pairs of a stack, in the order `pop` gives them. -/
def table.PairStack.pairs (st : table.PairStack) : List (Term × Term) :=
  (st.items.val.take st.len.val).reverse

theorem PairStack.pop_pairs_spec (st : table.PairStack) (hle : st.len.val ≤ st.items.val.length) :
    table.PairStack.pop st ⦃ r =>
      r.2.len.val ≤ r.2.items.val.length ∧ r.2.items = st.items ∧
      match r.1 with
      | none => st.pairs = [] ∧ r.2.pairs = []
      | some p => st.pairs = p :: r.2.pairs ⦄div := by
  unfold table.PairStack.pop
  split
  · rename_i h0
    simp only [WP.dspec_ok]
    have : st.len.val = 0 := by simp_all
    simp [table.PairStack.pairs, this]
  · rename_i h0
    have hpos : 0 < st.len.val := by
      have : st.len.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simp [h]))
      omega
    step as ⟨i, hi⟩
    step as ⟨p, hp⟩
    simp only [WP.dspec_ok]
    refine ⟨?_, ?_, ?_⟩
    · show i.val ≤ st.items.val.length; scalar_tac
    · trivial
    simp only [table.PairStack.pairs]
    have hlt : i.val < st.items.val.length := by scalar_tac
    have : st.len.val = i.val + 1 := by scalar_tac
    rw [this, List.take_succ_eq_append_getElem hlt, List.reverse_append, hp]
    simp

theorem PairStack.push_pairs_spec (st : table.PairStack) (pr : Term × Term)
    (hle : st.len.val ≤ st.items.val.length) (hroom : st.len.val + 1 < Usize.max) :
    table.PairStack.push st pr ⦃ st' =>
      st'.len.val ≤ st'.items.val.length ∧ st'.len.val = st.len.val + 1 ∧
      st'.pairs = pr :: st.pairs ∧ st'.items.val.length ≤ max st.items.val.length (st.len.val + 1) ⦄div := by
  unfold table.PairStack.push
  dsimp only
  by_cases hlt : st.len < alloc.vec.Vec.len st.items
  · simp only [hlt, ite_true]
    have hlt' : st.len.val < st.items.val.length := by scalar_tac
    rw [alloc.vec.Vec.index_mut_slice_index]
    simp only [Aeneas.Std.bind_assoc]
    apply WP.dspec_bind (WP.spec_dspec _ _ _ (alloc.vec.Vec.index_mut_usize_spec st.items st.len hlt'))
    rintro ⟨x, back⟩ ⟨hx, hback⟩
    step as ⟨i1, hi1⟩
    simp only [WP.dspec_ok]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show i1.val ≤ (back pr).val.length; simp_all
    · scalar_tac
    · simp only [table.PairStack.pairs]
      rw [show i1.val = st.len.val + 1 by scalar_tac]
      simp_all [List.take_succ_eq_append_getElem, List.take_set_of_le]
    · show (back pr).val.length ≤ _; simp_all
  · simp only [hlt, ite_false]
    step as ⟨v, hv⟩
    step as ⟨i1, hi1⟩
    simp only [WP.dspec_ok]
    have heq : st.len.val = st.items.val.length := by scalar_tac
    refine ⟨?_, ?_, ?_, ?_⟩
    · show i1.val ≤ v.val.length; simp_all
    · scalar_tac
    · simp only [table.PairStack.pairs]
      rw [show i1.val = st.len.val + 1 by scalar_tac]
      simp_all
    · show v.val.length ≤ _; simp_all


/-- The order of a list of pairs of trees: the first pair that differs. -/
noncomputable def pairsCmp : List (Tree × Tree) → Ordering
  | [] => .eq
  | (x, y) :: rest => (treeCmp x y).then (pairsCmp rest)

theorem Ordering.then_assoc' (a b c : Ordering) : (a.then b).then c = a.then (b.then c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem pairsCmp_append (l₁ l₂ : List (Tree × Tree)) :
    pairsCmp (l₁ ++ l₂) = (pairsCmp l₁).then (pairsCmp l₂) := by
  induction l₁ with
  | nil => simp only [List.nil_append, pairsCmp]; cases pairsCmp l₂ <;> rfl
  | cons p l ih => obtain ⟨x, y⟩ := p; simp [pairsCmp, ih, Ordering.then_assoc']

theorem listCmp_eq_pairsCmp : ∀ (xs ys : List Tree), xs.length = ys.length →
    listCmp xs ys = pairsCmp (xs.zip ys)
  | [], [], _ => by simp [listCmp, pairsCmp]
  | x :: xs, y :: ys, h => by
    simp only [listCmp, List.zip_cons_cons, pairsCmp]
    rw [listCmp_eq_pairsCmp xs ys (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The loop of `compare_step` that pushes the fields of two nodes, the last
first: the stack gives them in order. -/
theorem compare_step_loop_spec (xs ys : alloc.vec.Vec Term) (hl : xs.val.length = ys.val.length) :
    ∀ (i : Std.Usize) (todo : table.PairStack), i.val ≤ xs.val.length →
      todo.len.val ≤ todo.items.val.length → todo.len.val + i.val + 1 < Usize.max →
      Store.compare_step_loop todo xs ys i ⦃ todo' =>
        todo'.len.val ≤ todo'.items.val.length ∧ todo'.len.val = todo.len.val + i.val ∧
        todo'.pairs = (xs.val.take i.val).zip (ys.val.take i.val) ++ todo.pairs ⦄div := by
  intro i
  generalize hk : i.val = k
  induction k generalizing i with
  | zero =>
    intro todo _ hle _
    have hi : i = 0#usize := UScalar.eq_of_val_eq (by simp [hk])
    subst hi
    unfold Store.compare_step_loop
    simp only [show ¬ (0#usize > 0#usize) by decide, ite_false, WP.dspec_ok]
    simp [hle]
  | succ k ih =>
    intro todo hi hle hroom
    unfold Store.compare_step_loop
    have hpos : i > 0#usize := by
      show (0 : Nat) < i.val; omega
    simp only [hpos, ite_true]
    step as ⟨i1, hi1⟩
    have hk1 : i1.val = k := by omega
    have hlx : k < xs.val.length := by omega
    have hly : k < ys.val.length := by omega
    step as ⟨t, ht⟩
    step as ⟨t1, ht1⟩
    apply WP.dspec_bind (PairStack.push_pairs_spec todo (t, t1) hle (by omega))
    rintro todo1 ⟨hle1, hlen1, hp1, -⟩
    apply WP.dspec_mono (ih i1 hk1 todo1 (by omega) hle1 (by omega))
    rintro todo' ⟨hle', hlen', hp'⟩
    refine ⟨hle', by omega, ?_⟩
    rw [hp', hp1, ht, ht1, List.take_succ_eq_append_getElem hlx,
      List.take_succ_eq_append_getElem hly, List.zip_append (by simp; omega)]
    simp only [hk1]
    simp


/-- `order_key` looks at the root of the data only. -/
theorem order_key_holds {nodes : List TermData} {t : Nat} {x : Tree} (h : Holds nodes t x) :
    Store.order_key nodes[t]! = Store.order_key x.shape := by
  cases h <;> (rename_i hd; rw [hd]) <;> rfl


/-- The data of every term, and so of every tree root, has a key or an error
from `order_key`: what the calculus's tables give (`hok`, `hemb`). -/
theorem order_key_ok (hok : ∀ c, ∃ p, schema.Constructor.order_key c = ok p)
    (hemb : ∀ e, ∃ o, schema.Constructor.of_embedding e = ok o) (d : TermData) :
    ∃ r, Store.order_key d = ok r := by
  have hc : ∀ e, ∃ r, (do
      let o ← schema.Constructor.of_embedding e
      match o with
      | none => ok (core.result.Result.Err CheckError.InvalidConstructor)
      | some c => do
        let p ← schema.Constructor.order_key c
        ok (core.result.Result.Ok p) : Result _) = ok r := by
    intro e
    obtain ⟨o, ho⟩ := hemb e
    rw [ho, Std.bind_ok]
    cases o with
    | none => exact ⟨_, rfl⟩
    | some c => obtain ⟨p, hp⟩ := hok c; dsimp only; rw [hp, Std.bind_ok]; exact ⟨_, rfl⟩
  unfold Store.order_key
  cases d with
  | Stuck => exact hc _
  | Literal l => cases l <;> simp only [Std.bind_ok] <;> exact hc _
  | Native _ => exact ⟨_, rfl⟩
  | UserOp c => obtain ⟨p, hp⟩ := hok c; dsimp only; rw [hp, Std.bind_ok]; exact ⟨_, rfl⟩
  | Apply _ _ => exact hc _
  | Node c _ => obtain ⟨p, hp⟩ := hok c; dsimp only; rw [hp, Std.bind_ok]; exact ⟨_, rfl⟩

/-- Pairs of handles that stand for pairs of trees. -/
def PairsHold (nodes : List TermData) (hs : List (Term × Term)) (ts : List (Tree × Tree)) : Prop :=
  List.Forall₂ (fun p q => Holds nodes p.1.val q.1 ∧ Holds nodes p.2.val q.2) hs ts

theorem PairsHold.zip {nodes : List TermData} :
    ∀ {hs gs : List Term} {xs ys : List Tree}, HoldsList nodes hs xs → HoldsList nodes gs ys →
      PairsHold nodes (hs.zip gs) (xs.zip ys)
  | [], _, [], _, _, _ => by simp [PairsHold]
  | _ :: _, [], _ :: _, [], _, _ => by simp [PairsHold]
  | h :: hs, g :: gs, x :: xs, y :: ys, hh, hg => by
    cases hh with | cons _ _ _ _ h1 h2 =>
    cases hg with | cons _ _ _ _ g1 g2 =>
    exact List.Forall₂.cons ⟨h1, g1⟩ (PairsHold.zip h2 g2)
  | [], _, _ :: _, _, hh, _ => by cases hh
  | _ :: _, _, [], _, hh, _ => by cases hh
  | _ :: _, [], _ :: _, _ :: _, _, hg => by cases hg

/-- One step of `compare`: either it decides the order of the two trees, or
it leaves the stack with the pairs `new` on top, whose order is theirs. The
first handle of each new pair is below `a` (`Store.Wf`), and there are at
most `A` of them. -/
theorem compare_step_spec (s : Store) (hwf : s.Wf) (A : Nat) (hA2 : 2 ≤ A)
    (hA : ∀ c n, schema.Constructor.arity c = ok n → n.val ≤ A)
    (hok : ∀ c, ∃ p, schema.Constructor.order_key c = ok p)
    (hemb : ∀ e, ∃ o, schema.Constructor.of_embedding e = ok o)
    (a b : Term) (todo : table.PairStack) {ta tb : Tree}
    (ha : Holds s.nodes.val a.val ta) (hb : Holds s.nodes.val b.val tb)
    (hle : todo.len.val ≤ todo.items.val.length) (hroom : todo.len.val + A + 1 < Usize.max) :
    Store.compare_step s a b todo ⦃ r =>
      r.2.len.val ≤ r.2.items.val.length ∧
      ∀ o, r.1 = core.result.Result.Ok o →
        (o ≠ .eq ∧ treeCmp ta tb = o) ∨
        (o = .eq ∧ ∃ new ts, r.2.pairs = new ++ todo.pairs ∧ r.2.len.val = todo.len.val + new.length ∧
          new.length ≤ A ∧ (∀ p ∈ new, p.1.val < a.val) ∧
          PairsHold s.nodes.val new ts ∧ treeCmp ta tb = pairsCmp ts) ⦄div := by
  unfold Store.compare_step
  simp only [Term.Insts.CoreCmpPartialEqTerm.eq, Std.bind_ok]
  by_cases hab : a = b
  · subst hab
    have := Holds.functional ha hb; subst this
    simp only [decide_true, ite_true, WP.dspec_ok]
    refine ⟨hle, ?_⟩
    intro o ho; cases ho
    refine Or.inr ⟨rfl, ?_⟩
    exact ⟨[], [], by simp, by simp, by simp, by simp, List.Forall₂.nil,
      by rw [treeCmp_refl]; rfl⟩
  simp only [hab, decide_false, Bool.false_eq_true, ite_false]
  have hla := Holds.lt ha
  have hlb := Holds.lt hb
  simp only [Store.view_eq, hla, hlb, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨ra, hra⟩ := order_key_ok hok hemb s.nodes.val[a.val]!
  obtain ⟨rb, hrb⟩ := order_key_ok hok hemb s.nodes.val[b.val]!
  rw [hra, Std.bind_ok]
  cases ra with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, hle]
  | Ok ka =>
    simp only [Std.bind_ok]
    rw [hrb, Std.bind_ok]
    cases rb with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, hle]
    | Ok kb =>
      simp only [Std.bind_ok, lift]
      have hka : treeKey ta = some (ka.1.val, ka.2.val) := treeKey_of hok hemb (by rw [← order_key_holds ha]; exact hra)
      have hkb : treeKey tb = some (kb.1.val, kb.2.val) := treeKey_of hok hemb (by rw [← order_key_holds hb]; exact hrb)
      obtain ⟨i, i1⟩ := ka
      obtain ⟨i2, i3⟩ := kb
      have htags : treeCmp ta tb =
          match (compare i.val i2.val).then (compare i1.val i3.val) with
          | .eq => bodyCmp ta tb
          | o => o := by
        rw [treeCmp]; simp only [hka, hkb]
        rfl
      have htm : (match core.cmp.impls.OrdUsize.cmp i i2 with
          | Ordering.lt => ok Ordering.lt
          | Ordering.eq => ok (core.cmp.impls.OrdUsize.cmp i1 i3)
          | Ordering.gt => ok Ordering.gt : Result Ordering) =
          ok ((compare i.val i2.val).then (compare i1.val i3.val)) := by
        show (match compare i.val i2.val with
          | Ordering.lt => ok Ordering.lt
          | Ordering.eq => ok (compare i1.val i3.val)
          | Ordering.gt => ok Ordering.gt : Result Ordering) = _
        cases compare i.val i2.val <;> rfl
      show (do
        let tags ← (match core.cmp.impls.OrdUsize.cmp i i2 with
          | Ordering.lt => ok Ordering.lt
          | Ordering.eq => ok (core.cmp.impls.OrdUsize.cmp i1 i3)
          | Ordering.gt => ok Ordering.gt : Result Ordering)
        _) ⦃ _ ⦄div
      rw [htm, Std.bind_ok]
      generalize hT : (compare i.val i2.val).then (compare i1.val i3.val) = T at htags ⊢
      cases T with
      | lt =>
        simp only [WP.dspec_ok]
        refine ⟨hle, fun o h => ?_⟩
        cases h; left; exact ⟨by decide, htags⟩
      | gt =>
        simp only [WP.dspec_ok]
        refine ⟨hle, fun o h => ?_⟩
        cases h; left; exact ⟨by decide, htags⟩
      | eq =>
        simp only at htags
        cases ha <;> cases hb <;>
          rw [‹s.nodes.val[a.val]! = _›, ‹s.nodes.val[b.val]! = _›] <;>
          (try (simp [WP.dspec_ok, hle]; done))
        case neg.Ok.Ok.eq.lit.lit x _ _ y _ _ =>
          dsimp only
          apply WP.dspec_bind (literal_cmp_spec x y)
          intro r4 hr4
          simp only [WP.dspec_ok]
          refine ⟨hle, fun o ho => ?_⟩
          have hbody : treeCmp (Tree.lit x) (Tree.lit y) = o := by
            rw [htags, hr4 o ho]; simp [bodyCmp]
          by_cases hoe : o = .eq
          · refine Or.inr ⟨hoe, ?_⟩
            exact ⟨[], [], by simp, by simp, by simp, by simp, List.Forall₂.nil,
              by rw [hbody, hoe]; rfl⟩
          · left; exact ⟨hoe, hbody⟩
        case neg.Ok.Ok.eq.native.native x _ _ y _ _ =>
          dsimp only
          apply WP.dspec_bind (literal_cmp_spec x y)
          intro r4 hr4
          simp only [WP.dspec_ok]
          refine ⟨hle, fun o ho => ?_⟩
          have hbody : treeCmp (Tree.native x) (Tree.native y) = o := by
            rw [htags, hr4 o ho]; simp [bodyCmp]
          by_cases hoe : o = .eq
          · refine Or.inr ⟨hoe, ?_⟩
            exact ⟨[], [], by simp, by simp, by simp, by simp, List.Forall₂.nil,
              by rw [hbody, hoe]; rfl⟩
          · left; exact ⟨hoe, hbody⟩
        case neg.Ok.Ok.eq.userop.userop =>
          dsimp only
          simp only [WP.dspec_ok]
          refine ⟨hle, fun o ho => ?_⟩
          cases ho
          refine Or.inr ⟨rfl, ?_⟩
          exact ⟨[], [], by simp, by simp, by simp, by simp, List.Forall₂.nil, by rw [htags]; simp [bodyCmp, pairsCmp]⟩
        case neg.Ok.Ok.eq.apply.apply f x tx ty hf hx hlta hda g y ux uy hg hy hltb hdb =>
          dsimp only
          have hwa := hwf.wf a.val hlta
          rw [hda] at hwa
          obtain ⟨hfa, hxa, -, -⟩ := hwa
          simp only [List.length_take] at hfa hxa
          apply WP.dspec_bind (PairStack.push_pairs_spec todo (x, y) hle (by omega))
          rintro todo1 ⟨hle1, hlen1, hp1, -⟩
          apply WP.dspec_bind (PairStack.push_pairs_spec todo1 (f, g) hle1 (by omega))
          rintro todo2 ⟨hle2, hlen2, hp2, -⟩
          simp only [WP.dspec_ok]
          refine ⟨hle2, fun o ho => ?_⟩
          cases ho
          refine Or.inr ⟨rfl, ?_⟩
          refine ⟨[(f, g), (x, y)], [(tx, ux), (ty, uy)], by rw [hp2, hp1]; rfl, by simp; omega,
            by simp; omega, ?_, ?_, ?_⟩
          · intro p hp
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl <;> simp <;> omega
          · exact List.Forall₂.cons ⟨hf, hg⟩ (List.Forall₂.cons ⟨hx, hy⟩ List.Forall₂.nil)
          · rw [htags]; simp only [bodyCmp, pairsCmp]
            cases treeCmp ty uy <;> simp [Ordering.then]
        case neg.Ok.Ok.eq.node.node c v xs hxs hlta hda c' w ys hys hltb hdb =>
          dsimp only
          have hwa := hwf.wf a.val hlta
          rw [hda] at hwa
          obtain ⟨hfa, ⟨n, har, hn⟩, -⟩ := hwa
          have hvA : v.val.length ≤ A := by
            have := hA c n har; simp [alloc.vec.Vec.length] at hn; omega
          have hlx := hxs.length
          have hly := hys.length
          by_cases hl : v.val.length = w.val.length
          · have hl' : alloc.vec.Vec.len v = alloc.vec.Vec.len w :=
              UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len, hl])
            simp only [hl', bne_self_eq_false, Bool.false_eq_true, ite_false]
            apply WP.dspec_bind (compare_step_loop_spec v w hl (alloc.vec.Vec.len w) todo
              (by simp [alloc.vec.Vec.len, hl]) hle (by simp [alloc.vec.Vec.len]; omega))
            rintro todo1 ⟨hle1, hlen1, hp1⟩
            simp only [WP.dspec_ok]
            refine ⟨hle1, fun o ho => ?_⟩
            cases ho
            refine Or.inr ⟨rfl, ?_⟩
            have hlw : (alloc.vec.Vec.len w).val = w.val.length := by simp [alloc.vec.Vec.len]
            have hlv : (alloc.vec.Vec.len w).val = v.val.length := by rw [hlw, hl]
            refine ⟨v.val.zip w.val, xs.zip ys, ?_, ?_, ?_, ?_, PairsHold.zip hxs hys, ?_⟩
            · rw [hp1]; congr 2
              · rw [hlv, List.take_length]
              · rw [hlw, List.take_length]
            · rw [hlen1, hlv]; simp [hl]
            · simp; omega
            · intro p hp
              have := hfa p.1 (List.of_mem_zip hp).1
              simp only [List.length_take] at this; omega
            · rw [htags]; simp only [bodyCmp]
              rw [if_pos (by omega), listCmp_eq_pairsCmp xs ys (by omega)]
          · have hl' : ¬ alloc.vec.Vec.len v = alloc.vec.Vec.len w := by
              intro h; apply hl; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len] using this
            simp [hl', hle]


/-! ## The size of the stack

`compare` pops a pair and pushes the fields of its two terms, whose handles
are below the first handle of the pair (`Store.Wf`). So the stack is always
blocks of at most `A` pairs (the largest arity), each block's first handles
below a bound, and the bounds strictly increase: at most `A * (M + 1)`
pairs for handles below `M`. -/

/-- The pairs `ps` are the blocks `bs`, in order. -/
def Blocks (A : Nat) (ps : List (Term × Term)) (bs : List (List (Term × Term) × Nat)) : Prop :=
  ps = (bs.map Prod.fst).flatten ∧ (∀ b ∈ bs, b.1.length ≤ A ∧ ∀ p ∈ b.1, p.1.val < b.2) ∧
    (bs.map Prod.snd).Pairwise (· < ·)

theorem pairwise_lt_length_le : ∀ (M : Nat) (l : List Nat), l.Pairwise (· < ·) → (∀ x ∈ l, x ≤ M) →
    l.length ≤ M + 1
  | M, [], _, _ => by simp
  | M, x :: l, hp, hb => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hx, hl⟩ := hp
    -- the rest are above `x`, so at most `M - x` of them
    have hpos : ∀ y ∈ l, 1 ≤ y := fun y hy => by have := hx y hy; omega
    cases M with
    | zero =>
      cases l with
      | nil => simp
      | cons y l => have := hx y (by simp); have := hb y (by simp); omega
    | succ M =>
      have ih := pairwise_lt_length_le M (l.map (· - 1))
        (by
          rw [List.pairwise_map]
          exact hl.imp_of_mem (fun {a b} ha hb' hab => by
            have := hpos a ha; have := hpos b hb'; omega))
        (by
          intro y hy
          rw [List.mem_map] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          have := hb z (by simp [hz]); omega)
      simp at ih ⊢; omega

theorem Blocks.length_le {A M : Nat} {ps : List (Term × Term)} {bs : List (List (Term × Term) × Nat)}
    (h : Blocks A ps bs) (hM : ∀ b ∈ bs, b.2 ≤ M) : ps.length ≤ A * (M + 1) := by
  obtain ⟨rfl, hb, hp⟩ := h
  have hlen : (bs.map Prod.fst).flatten.length ≤ A * bs.length := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have h1 := (hb b (by simp)).1
      have h2 := ih (fun b' hb' => hM b' (by simp [hb'])) (fun b' hb' => hb b' (by simp [hb']))
        (by simp at hp; exact hp.2)
      rw [Nat.mul_succ]; omega
  have hbs : bs.length ≤ M + 1 := by
    have := pairwise_lt_length_le M (bs.map Prod.snd) hp
      (by intro y hy; rw [List.mem_map] at hy; obtain ⟨b, hb', rfl⟩ := hy; exact hM b hb')
    simpa using this
  calc _ ≤ A * bs.length := hlen
    _ ≤ A * (M + 1) := Nat.mul_le_mul_left _ hbs

/-- A pop and a push of at most `A` pairs below the popped pair's first
handle keep the blocks. -/
theorem Blocks.step {A M : Nat} {p : Term × Term} {rest : List (Term × Term)} :
    ∀ {bs : List (List (Term × Term) × Nat)}, Blocks A (p :: rest) bs → (∀ b ∈ bs, b.2 ≤ M) →
      ∀ (new : List (Term × Term)), new.length ≤ A → (∀ q ∈ new, q.1.val < p.1.val) →
      ∃ bs', Blocks A (new ++ rest) bs' ∧ ∀ b ∈ bs', b.2 ≤ M
  | [], h, _, _, _, _ => by simp [Blocks] at h
  | (b, m) :: post, ⟨hps, hb, hp⟩, hM, new, hnew, hlt => by
    cases b with
    | nil =>
      -- an empty block: the pair is in the rest
      exact Blocks.step (bs := post) ⟨by simpa using hps, fun b' hb' => hb b' (by simp [hb']),
        by simp at hp; exact hp.2⟩ (fun b' hb' => hM b' (by simp [hb'])) new hnew hlt
    | cons q r =>
      simp only [List.map_cons, List.flatten_cons, List.cons_append, List.cons.injEq] at hps
      obtain ⟨rfl, hrest⟩ := hps
      have hpm : p.1.val < m := (hb (p :: r, m) (by simp)).2 p (by simp)
      refine ⟨(new, p.1.val) :: (r, m) :: post, ⟨?_, ?_, ?_⟩, ?_⟩
      · simp [hrest]
      · intro b' hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with rfl | rfl | hb'
        · exact ⟨hnew, hlt⟩
        · have := hb (p :: r, m) (by simp)
          exact ⟨by show r.length ≤ A; simp at this; omega, fun q hq => this.2 q (by simp [hq])⟩
        · exact hb b' (by simp [hb'])
      · simp only [List.map_cons, List.pairwise_cons] at hp ⊢
        refine ⟨?_, hp⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hpm
        · exact Nat.lt_trans hpm (hp.1 x hx)
      · intro b' hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with rfl | rfl | hb'
        · show p.1.val ≤ M
          have := hM (p :: r, m) (by simp); simp only at this; omega
        · exact hM (p :: r, m) (by simp)
        · exact hM b' (by simp [hb'])


theorem PairsHold.append {nodes : List TermData} :
    ∀ {hs hs' : List (Term × Term)} {ts ts' : List (Tree × Tree)},
      PairsHold nodes hs ts → PairsHold nodes hs' ts' → PairsHold nodes (hs ++ hs') (ts ++ ts')
  | [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, .cons h hs, h' => .cons h (PairsHold.append hs h')

theorem PairStack.pairs_length (st : table.PairStack) (h : st.len.val ≤ st.items.val.length) :
    st.pairs.length = st.len.val := by
  simp [table.PairStack.pairs, List.length_take, h]

/-- The loop of `compare`: while it goes on (`more`), what is left on the
stack decides the answer; when it stops, `result` is the answer. -/
theorem compare_loop_spec (s : Store) (hwf : s.Wf) (hmax : s.nodes.val.length ≤ U32.max)
    (h64 : Platform64) (A : Nat) (hA2 : 2 ≤ A) (hA100 : A ≤ 100)
    (hA : ∀ c n, schema.Constructor.arity c = ok n → n.val ≤ A)
    (hok : ∀ c, ∃ p, schema.Constructor.order_key c = ok p)
    (hemb : ∀ e, ∃ o, schema.Constructor.of_embedding e = ok o) (ans : Ordering) :
    ∀ (todo : table.PairStack) (result : Ordering) (more : Bool),
      todo.len.val ≤ todo.items.val.length →
      (more = false → result = ans) →
      (more = true → result = .eq ∧ ∃ ts bs, PairsHold s.nodes.val todo.pairs ts ∧
        pairsCmp ts = ans ∧ Blocks A todo.pairs bs ∧ ∀ b ∈ bs, b.2 ≤ s.nodes.val.length) →
      Store.compare_loop s todo result more ⦃ r => ∀ o, r = core.result.Result.Ok o → o = ans ⦄div := by
  apply Store.compare_loop.fixpoint_induct s
    (motive := fun loop => ∀ (todo : table.PairStack) (result : Ordering) (more : Bool),
      todo.len.val ≤ todo.items.val.length →
      (more = false → result = ans) →
      (more = true → result = .eq ∧ ∃ ts bs, PairsHold s.nodes.val todo.pairs ts ∧
        pairsCmp ts = ans ∧ Blocks A todo.pairs bs ∧ ∀ b ∈ bs, b.2 ≤ s.nodes.val.length) →
      loop todo result more ⦃ r => ∀ o, r = core.result.Result.Ok o → o = ans ⦄div)
  · prove_adm
  · intro loop ih todo result more hle hfalse htrue
    beta_reduce
    cases more with
    | false =>
      simp only [Bool.false_eq_true, ite_false, WP.dspec_ok]
      intro o ho; cases ho; exact hfalse rfl
    | true =>
      obtain ⟨hres, ts, bs, hph, hans, hbl, hbM⟩ := htrue rfl
      subst hres
      simp only [ite_true]
      apply WP.dspec_bind (PairStack.pop_pairs_spec todo hle)
      rintro ⟨o, todo1⟩ ⟨hle1, hitems, hpop⟩
      cases o with
      | none =>
        obtain ⟨hnil, -⟩ := hpop
        apply ih todo1 .eq false hle1 (fun _ => ?_) (fun h => by cases h)
        rw [hnil] at hph
        cases hph; rw [← hans]; rfl
      | some pr =>
        obtain ⟨a, b⟩ := pr
        simp only at hpop ⊢
        rw [hpop] at hph hbl
        cases hph with | cons hab hrest =>
        rename_i tab ts'
        obtain ⟨ta, tb⟩ := tab
        obtain ⟨ha, hb⟩ := hab
        -- room on the stack: at most A * (M + 1) pairs
        have hlen0 := Blocks.length_le hbl hbM
        have hlen1 := PairStack.pairs_length todo1 hle1
        have hlenp : todo.pairs.length = todo1.pairs.length + 1 := by rw [hpop]; simp
        have hroom : todo1.len.val + A + 1 < Usize.max := by
          have : (2 : Nat) ^ 40 ≤ Usize.max := h64
          have hM : s.nodes.val.length ≤ 2 ^ 32 - 1 := by
            have : U32.max = 2 ^ 32 - 1 := by simp [U32.max, U32.numBits]
            omega
          have : (a, b) :: todo1.pairs = todo.pairs := hpop.symm
          have hl2 : ((a, b) :: todo1.pairs).length ≤ A * (s.nodes.val.length + 1) := by
            exact hlen0
          simp at hl2
          have : A * (s.nodes.val.length + 1) ≤ 100 * 2 ^ 32 := by
            calc A * (s.nodes.val.length + 1) ≤ 100 * (s.nodes.val.length + 1) := Nat.mul_le_mul_right _ hA100
              _ ≤ 100 * 2 ^ 32 := Nat.mul_le_mul_left _ (by omega)
          omega
        apply WP.dspec_bind (compare_step_spec s hwf A hA2 hA hok hemb a b todo1 ha hb hle1 hroom)
        rintro ⟨r, todo2⟩ ⟨hle2, hr⟩
        cases r with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch]
        | Ok o =>
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          have hstep := hr o rfl
          have hans' : ans = (treeCmp ta tb).then (pairsCmp ts') := by rw [← hans]; rfl
          cases o with
          | lt =>
            apply ih todo2 .lt false hle2 (fun _ => ?_) (fun h => by cases h)
            rcases hstep with ⟨-, hc⟩ | ⟨ho, -⟩
            · rw [hans', hc]; rfl
            · cases ho
          | gt =>
            apply ih todo2 .gt false hle2 (fun _ => ?_) (fun h => by cases h)
            rcases hstep with ⟨-, hc⟩ | ⟨ho, -⟩
            · rw [hans', hc]; rfl
            · cases ho
          | eq =>
            apply ih todo2 .eq true hle2 (fun h => by cases h) (fun _ => ?_)
            refine ⟨rfl, ?_⟩
            rcases hstep with ⟨hne, -⟩ | ⟨-, new, tsn, hp2, -, hnA, hnlt, hnh, hc⟩
            · exact absurd rfl hne
            · obtain ⟨bs', hbl', hbM'⟩ := Blocks.step hbl hbM new hnA hnlt
              refine ⟨tsn ++ ts', bs', ?_, ?_, ?_, hbM'⟩
              · rw [hp2]; exact PairsHold.append hnh hrest
              · rw [pairsCmp_append, ← hc, hans']
              · rw [hp2]; exact hbl'

theorem PairStack.new_pairs_spec :
    table.PairStack.new ⦃ p => p.len.val = 0 ∧ p.items.val = [] ⦄ := by
  unfold table.PairStack.new; simp

/-- `compare` on two terms of a store gives the order of their trees. -/
theorem compare_spec (s : Store) (hinv : s.Inv) (h64 : Platform64)
    (A : Nat) (hA2 : 2 ≤ A) (hA100 : A ≤ 100)
    (hA : ∀ c n, schema.Constructor.arity c = ok n → n.val ≤ A)
    (hok : ∀ c, ∃ p, schema.Constructor.order_key c = ok p)
    (hemb : ∀ e, ∃ o, schema.Constructor.of_embedding e = ok o)
    (a b : Term) {ta tb : Tree}
    (ha : Holds s.nodes.val a.val ta) (hb : Holds s.nodes.val b.val tb) :
    Store.compare s a b ⦃ r => ∀ o, r = core.result.Result.Ok o → o = treeCmp ta tb ⦄div := by
  unfold Store.compare
  apply WP.dspec_bind (WP.spec_dspec _ _ _ PairStack.new_pairs_spec)
  rintro todo ⟨h0, hitems⟩
  have hU : (2 : Nat) ^ 40 ≤ Usize.max := h64
  apply WP.dspec_bind (PairStack.push_pairs_spec todo (a, b) (by omega) (by omega))
  rintro todo1 ⟨hle1, -, hp1, -⟩
  have hnil : todo.pairs = [] := by simp [table.PairStack.pairs, h0]
  rw [hnil] at hp1
  have hmax : s.nodes.val.length ≤ U32.max := by
    have := hinv.table.hmax; simpa [alloc.vec.Vec.length] using this
  have hla := Holds.lt ha
  apply compare_loop_spec s hinv.terms hmax h64 A hA2 hA100 hA hok hemb (treeCmp ta tb)
    todo1 .eq true hle1 (fun h => by cases h)
  intro _
  refine ⟨rfl, [(ta, tb)], [([(a, b)], a.val + 1)], ?_, ?_, ?_, ?_⟩
  · rw [hp1]; exact List.Forall₂.cons ⟨ha, hb⟩ List.Forall₂.nil
  · simp [pairsCmp]
  · rw [hp1]
    refine ⟨by simp, ?_, by simp⟩
    intro b' hb'; simp at hb'; subst hb'; simp; omega
  · intro b' hb'; simp at hb'; subst hb'; simp; omega

end pathos_compiled_checker
