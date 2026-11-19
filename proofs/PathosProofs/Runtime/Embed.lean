module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame

/-!
# Handles and logos's other values

A program of the checker takes and gives not only terms: proofs, the
checker's state and its objects, native Booleans. Each is embedded in the
store as terms are, and each has its relation between a handle and logos's
value. `Represents` names the relation of a type, so that a generated
theorem need not: Lean finds it from the program's signature.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result


/-- The handle `t` stands for the proof `p`: a node `$eo_pf` over a handle
of the proved formula. -/
inductive RepProof (s : Store) : Term → Eo.Proof → Prop where
  | pf (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length → s.data t = TermData.Node schema.Constructor.eo__24eo_5fpf v →
      v.val = [f] → s.Rep f F → RepProof s t (Eo.Proof.pf F)
  | stuck (t : Term) :
      t.val < s.nodes.length → s.data t = TermData.Stuck → RepProof s t Eo.Proof.Stuck

theorem RepProof.congr {s s' : Store} {t : Term} {p : Eo.Proof} (h : RepProof s t p)
    (hn : s'.nodes = s.nodes) : RepProof s' t p := by
  cases h with
  | pf f v F hlt hd hv hf =>
    exact RepProof.pf t f v F (by rw [hn]; exact hlt) (by unfold Store.data; rw [hn]; exact hd) hv
      (hf.congr hn)
  | stuck hlt hd =>
    exact RepProof.stuck t (by rw [hn]; exact hlt) (by unfold Store.data; rw [hn]; exact hd)

/-- `destruct` with `$eo_pf` on a handle of a proof. -/
theorem RepProof.destruct {s : Store} {t : Term} {p : Eo.Proof} (h : RepProof s t p) :
    (∃ f v F, p = Eo.Proof.pf F ∧ v.val = [f] ∧ s.Rep f F ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t
        = ok (core.result.Result.Ok (some v), s)) ∨
    (p = Eo.Proof.Stuck ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t = ok (core.result.Result.Ok none, s)) := by
  rw [Store.destruct_data_eq s _ t rfl]
  cases h with
  | pf f v F hlt hd hv hf =>
    left
    exact ⟨f, v, F, rfl, hv, hf, by simp [hlt, hd]⟩
  | stuck hlt hd =>
    right
    exact ⟨rfl, by simp [hlt, hd]⟩


/-- The handle `t` stands for the state object `o`. -/
inductive RepObj (s : Store) : Term → Eo.CStateObj → Prop where
  | assume (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fso_2eassume v →
      v.val = [f] → s.Rep f F → RepObj s t (Eo.CStateObj.assume F)
  | assume_push (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fso_2eassume_5fpush v →
      v.val = [f] → s.Rep f F → RepObj s t (Eo.CStateObj.assume_push F)
  | proven (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fso_2eproven v →
      v.val = [f] → s.Rep f F → RepObj s t (Eo.CStateObj.proven F)

/-- The handle `t` stands for the state `S`. -/
inductive RepState (s : Store) : Term → Eo.CState → Prop where
  | nil (t : Term) (v : alloc.vec.Vec Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fs_2enil v → v.val = [] →
      RepState s t Eo.CState.nil
  | cons (t so tl : Term) (v : alloc.vec.Vec Term) (o : Eo.CStateObj) (S : Eo.CState) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fs_2econs v → v.val = [so, tl] →
      RepObj s so o → RepState s tl S → RepState s t (Eo.CState.cons o S)
  | stuck (t : Term) (v : alloc.vec.Vec Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fs_2eStuck v → v.val = [] →
      RepState s t Eo.CState.Stuck

/-- The handle `t` is the native Boolean `b`. -/
def NativeBool (s : Store) (t : Term) (b : Bool) : Prop :=
  t.val < s.nodes.length ∧ s.data t = TermData.Native (lit.Lit.Boolean b)

theorem Store.data_grows {s s' : Store} (hg : s.nodes.val <+: s'.nodes.val) (t : Term)
    (hlt : t.val < s.nodes.length) : s'.data t = s.data t := by
  obtain ⟨r, hr⟩ := hg
  unfold Store.data
  rw [← hr]; exact getElem!_append_left _ _ _ hlt

theorem Store.lt_grows {s s' : Store} (hg : s.nodes.val <+: s'.nodes.val) {t : Term}
    (hlt : t.val < s.nodes.length) : t.val < s'.nodes.length :=
  Nat.lt_of_lt_of_le hlt hg.length_le

theorem RepObj.mono {s s' : Store} {t : Term} {o : Eo.CStateObj} (h : RepObj s t o)
    (hg : s.nodes.val <+: s'.nodes.val) : RepObj s' t o := by
  cases h with
  | assume f v F hlt hd hv hf =>
    exact RepObj.assume t f v F (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd)
      hv (Rep.mono hg hf)
  | assume_push f v F hlt hd hv hf =>
    exact RepObj.assume_push t f v F (Store.lt_grows hg hlt)
      (by rw [Store.data_grows hg t hlt]; exact hd) hv (Rep.mono hg hf)
  | proven f v F hlt hd hv hf =>
    exact RepObj.proven t f v F (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd)
      hv (Rep.mono hg hf)

theorem RepState.mono {s s' : Store} {t : Term} {S : Eo.CState} (h : RepState s t S)
    (hg : s.nodes.val <+: s'.nodes.val) : RepState s' t S := by
  induction h with
  | nil t v hlt hd hv =>
    exact RepState.nil t v (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd) hv
  | cons t so tl v o S hlt hd hv ho _ ih =>
    exact RepState.cons t so tl v o S (Store.lt_grows hg hlt)
      (by rw [Store.data_grows hg t hlt]; exact hd) hv (ho.mono hg) ih
  | stuck t v hlt hd hv =>
    exact RepState.stuck t v (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd) hv

theorem NativeBool.mono {s s' : Store} {t : Term} {b : Bool} (h : NativeBool s t b)
    (hg : s.nodes.val <+: s'.nodes.val) : NativeBool s' t b :=
  ⟨Store.lt_grows hg h.1, by rw [Store.data_grows hg t h.1]; exact h.2⟩


theorem NativeBool.congr {s s' : Store} {t : Term} {b : Bool} (h : NativeBool s t b)
    (hn : s'.nodes = s.nodes) : NativeBool s' t b := by
  unfold NativeBool Store.data at h ⊢
  rw [hn]; exact h

theorem RepState.congr {s s' : Store} {t : Term} {S : Eo.CState} (h : RepState s t S)
    (hn : s'.nodes = s.nodes) : RepState s' t S :=
  h.mono (by rw [hn])


theorem RepProof.mono {s s' : Store} {t : Term} {p : Eo.Proof} (h : RepProof s t p)
    (hg : s.nodes.val <+: s'.nodes.val) : RepProof s' t p := by
  cases h with
  | pf f v F hlt hd hv hf =>
    exact RepProof.pf t f v F (Store.lt_grows hg hlt)
      (by rw [Store.data_grows hg t hlt]; exact hd) hv (Rep.mono hg hf)
  | stuck hlt hd =>
    exact RepProof.stuck t (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd)

theorem RepObj.congr {s s' : Store} {t : Term} {o : Eo.CStateObj} (h : RepObj s t o)
    (hn : s'.nodes = s.nodes) : RepObj s' t o :=
  h.mono (by rw [hn])

/-- How a handle stands for a value of the type `α`. The generated theorems
are stated with it. -/
class Represents (α : Type) where
  rep : Store → Term → α → Prop

@[reducible] instance : Represents Eo.Term := ⟨fun s t x => s.Rep t x⟩
@[reducible] instance : Represents Eo.Proof := ⟨RepProof⟩
@[reducible] instance : Represents Eo.CStateObj := ⟨RepObj⟩
@[reducible] instance : Represents Eo.CState := ⟨RepState⟩
@[reducible] instance : Represents Bool := ⟨NativeBool⟩

@[simp] theorem Represents.rep_term (s : Store) (t : Term) (x : Eo.Term) :
    Represents.rep s t x = s.Rep t x := rfl
@[simp] theorem Represents.rep_proof (s : Store) (t : Term) (x : Eo.Proof) :
    Represents.rep s t x = RepProof s t x := rfl
@[simp] theorem Represents.rep_state (s : Store) (t : Term) (x : Eo.CState) :
    Represents.rep s t x = RepState s t x := rfl
@[simp] theorem Represents.rep_obj (s : Store) (t : Term) (x : Eo.CStateObj) :
    Represents.rep s t x = RepObj s t x := rfl
@[simp] theorem Represents.rep_bool (s : Store) (t : Term) (x : Bool) :
    Represents.rep s t x = NativeBool s t x := rfl

/-- The value that a program gives when none of its cases applies, in the
types that have one. (A program to a type without one has a case for
every argument, and the value here is never used.) -/
class HasStuck (α : Type) where
  stuck : α

instance : HasStuck Eo.Term := ⟨Eo.Term.Stuck⟩
instance : HasStuck Eo.Proof := ⟨Eo.Proof.Stuck⟩
instance : HasStuck Bool := ⟨false⟩

/-! ## Values that a store can hold

logos's functions are defined on every value of their types, among them
terms that no store holds: an application of the stuck term, or to it.
`apply` never makes one. Where a function of logos and the generated code
differ only on such values, the proofs say so with `Valid`. -/

/-- No application in the term is of the stuck term or to it. -/
def TermValid : Eo.Term → Prop
  | Eo.Term.Apply f a => f ≠ Eo.Term.Stuck ∧ a ≠ Eo.Term.Stuck ∧ TermValid f ∧ TermValid a
  | _ => True

/-- The values of a type that a store can hold. -/
class Valid (α : Type) where
  valid : α → Prop

instance : Valid Eo.Term := ⟨TermValid⟩
instance : Valid Eo.Proof := ⟨fun p => match p with | Eo.Proof.pf F => TermValid F | _ => True⟩
instance : Valid Eo.CStateObj := ⟨fun _ => True⟩
instance : Valid Eo.CState := ⟨fun _ => True⟩
instance : Valid Bool := ⟨fun _ => True⟩

@[simp] theorem Valid.apply (f a : Eo.Term) :
    Valid.valid (Eo.Term.Apply f a) ↔
      f ≠ Eo.Term.Stuck ∧ a ≠ Eo.Term.Stuck ∧ Valid.valid f ∧ Valid.valid a := by
  show TermValid _ ↔ _ ∧ _ ∧ TermValid _ ∧ TermValid _
  simp [TermValid]

@[simp] theorem Valid.pf (F : Eo.Term) : Valid.valid (Eo.Proof.pf F) ↔ Valid.valid F := Iff.rfl

theorem Rep.valid {s : Store} (hinv : s.Inv) {k : Nat} {x : Eo.Term}
    (h : Rep s.nodes.val k x) : TermValid x := by
  induction h with
  | stuck => trivial
  | uop => trivial
  | boolean => trivial
  | apply t f a x y hlt hd hf ha ihf iha =>
    have hwf := hinv.terms.data t hlt
    rw [hd] at hwf
    obtain ⟨_, _, h3, h4⟩ := hwf
    refine ⟨?_, ?_, ihf, iha⟩
    · intro hx; subst hx; cases hf with | stuck _ _ hd' => exact h3 hd'
    · intro hy; subst hy; cases ha with | stuck _ _ hd' => exact h4 hd'

theorem Store.Rep.valid {s : Store} (hinv : s.Inv) {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    Valid.valid x := pathos_compiled_checker.Rep.valid hinv h

theorem RepProof.valid {s : Store} (hinv : s.Inv) {t : Term} {p : Eo.Proof}
    (h : RepProof s t p) : Valid.valid p := by
  cases h with
  | pf f v F hlt hd hv hf => exact pathos_compiled_checker.Rep.valid hinv hf
  | stuck => trivial

/-! ## Equal handles, equal values -/

theorem Store.node_inj {s : Store} (hinv : s.Inv) {t u : Term} (ht : t.val < s.nodes.length)
    (hu : u.val < s.nodes.length) (h : s.data t = s.data u) : t = u :=
  u32_eq_of_val (hinv.table.nodup t.val u.val ht hu h)

theorem RepObj.functional {s : Store} {t : Term} {o o' : Eo.CStateObj} (h : RepObj s t o)
    (h' : RepObj s t o') : o = o' := by
  cases h with
  | assume f v F hlt hd hv hf =>
    cases h' with
    | assume f' v' F' _ hd' hv' hf' =>
      rw [hd] at hd'
      injection hd' with _ h2
      subst h2
      rw [hv] at hv'
      injection hv' with h3 _
      subst h3
      rw [Rep.functional hf hf']
    | assume_push _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | proven _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
  | assume_push f v F hlt hd hv hf =>
    cases h' with
    | assume _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | assume_push f' v' F' _ hd' hv' hf' =>
      rw [hd] at hd'
      injection hd' with _ h2
      subst h2
      rw [hv] at hv'
      injection hv' with h3 _
      subst h3
      rw [Rep.functional hf hf']
    | proven _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
  | proven f v F hlt hd hv hf =>
    cases h' with
    | assume _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | assume_push _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | proven f' v' F' _ hd' hv' hf' =>
      rw [hd] at hd'
      injection hd' with _ h2
      subst h2
      rw [hv] at hv'
      injection hv' with h3 _
      subst h3
      rw [Rep.functional hf hf']

theorem RepObj.injective {s : Store} (hinv : s.Inv) {t u : Term} {o : Eo.CStateObj}
    (h : RepObj s t o) (h' : RepObj s u o) : t = u := by
  cases h with
  | assume f v F hlt hd hv hf =>
    cases h' with
    | assume f' v' _ hlt' hd' hv' hf' =>
      have hff : f = f' := (Store.Rep.eq_iff hinv hf hf').mpr rfl
      subst hff
      have hvv : v = v' := alloc.vec.Vec.ext _ _ (by rw [hv, hv'])
      subst hvv
      exact Store.node_inj hinv hlt hlt' (by rw [hd, hd'])
  | assume_push f v F hlt hd hv hf =>
    cases h' with
    | assume_push f' v' _ hlt' hd' hv' hf' =>
      have hff : f = f' := (Store.Rep.eq_iff hinv hf hf').mpr rfl
      subst hff
      have hvv : v = v' := alloc.vec.Vec.ext _ _ (by rw [hv, hv'])
      subst hvv
      exact Store.node_inj hinv hlt hlt' (by rw [hd, hd'])
  | proven f v F hlt hd hv hf =>
    cases h' with
    | proven f' v' _ hlt' hd' hv' hf' =>
      have hff : f = f' := (Store.Rep.eq_iff hinv hf hf').mpr rfl
      subst hff
      have hvv : v = v' := alloc.vec.Vec.ext _ _ (by rw [hv, hv'])
      subst hvv
      exact Store.node_inj hinv hlt hlt' (by rw [hd, hd'])

theorem RepObj.eq_iff {s : Store} {t u : Term} {o o' : Eo.CStateObj} (hinv : s.Inv)
    (h : RepObj s t o) (h' : RepObj s u o') : t = u ↔ o = o' :=
  ⟨fun e => by subst e; exact h.functional h', fun e => by subst e; exact h.injective hinv h'⟩

theorem RepState.functional {s : Store} {t : Term} {S S' : Eo.CState} (h : RepState s t S)
    (h' : RepState s t S') : S = S' := by
  induction h generalizing S' with
  | nil t v hlt hd hv =>
    cases h' with
    | nil => rfl
    | cons _ _ _ _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | stuck _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
  | cons t so tl v o S hlt hd hv ho _ ih =>
    cases h' with
    | nil _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | cons _ so' tl' v' o' S'' _ hd' hv' ho' hS' =>
      rw [hd] at hd'
      injection hd' with _ h2
      subst h2
      rw [hv] at hv'
      injection hv' with h3 h4
      injection h4 with h5 _
      subst h3; subst h5
      rw [ho.functional ho', ih hS']
    | stuck _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
  | stuck t v hlt hd hv =>
    cases h' with
    | nil _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | cons _ _ _ _ _ _ _ hd' => rw [hd] at hd'; injection hd' with h1 _; cases h1
    | stuck => rfl

theorem RepState.injective {s : Store} (hinv : s.Inv) {t u : Term} {S : Eo.CState}
    (h : RepState s t S) (h' : RepState s u S) : t = u := by
  induction h generalizing u with
  | nil t v hlt hd hv =>
    cases h' with
    | nil _ v' hlt' hd' hv' =>
      have hvv : v = v' := alloc.vec.Vec.ext _ _ (by rw [hv, hv'])
      subst hvv
      exact Store.node_inj hinv hlt hlt' (by rw [hd, hd'])
  | cons t so tl v o S hlt hd hv ho _ ih =>
    cases h' with
    | cons _ so' tl' v' _ _ hlt' hd' hv' ho' hS' =>
      have h1 : so = so' := ho.injective hinv ho'
      have h2 : tl = tl' := ih hS'
      subst h1; subst h2
      have hvv : v = v' := alloc.vec.Vec.ext _ _ (by rw [hv, hv'])
      subst hvv
      exact Store.node_inj hinv hlt hlt' (by rw [hd, hd'])
  | stuck t v hlt hd hv =>
    cases h' with
    | stuck _ v' hlt' hd' hv' =>
      have hvv : v = v' := alloc.vec.Vec.ext _ _ (by rw [hv, hv'])
      subst hvv
      exact Store.node_inj hinv hlt hlt' (by rw [hd, hd'])

theorem RepState.eq_iff {s : Store} {t u : Term} {S S' : Eo.CState} (hinv : s.Inv)
    (h : RepState s t S) (h' : RepState s u S') : t = u ↔ S = S' :=
  ⟨fun e => by subst e; exact h.functional h', fun e => by subst e; exact h.injective hinv h'⟩

end pathos_compiled_checker
