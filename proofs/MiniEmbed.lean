module

public import MiniChecker
public import PathosProofs.Store.Tree
public import CpcMini.Logos
public import CpcMini.SmtTranslate

/-!
How the Rust checker that rust-meta compiles stores the values of the
checker: for each datatype `T` of the embedding, `enc_T` is the tree of the
store (`Tree`, in pathos's proofs) that a value is stored as, `dec_T` reads
a value back from a tree, and `dec_enc_T` says that it gets every value
back that the store can hold (`emb_T`: its native strings and bit-vectors
fit the runtime's). So `enc_T` is injective there: equal trees, equal
values.

A constructor is stored as the runtime's `Constructor::embedding` says: the
stuck term, an application, an object literal, a user operator as a node of
its own constructor with no fields, and every other constructor as a node
over its fields, natives as native literals.

Written by lean-meta with the case file, for pathos's proofs (its
`MiniEmbed.lean`); `MiniChecker` is the Lean of the compiled checker.
Nothing in logos uses it.
-/

@[expose] public section

set_option linter.unusedVariables false
set_option linter.internalConstructors false
set_option maxHeartbeats 10000000

namespace pathos_compiled_checker.Embed

open Aeneas Aeneas.Std

noncomputable section

/-! Not embedded (a field or a constructor that has no encoding):
- `SmtMap`: the field SmtValue of cons
- `SmtRegLan`: the field SmtValue of char
- `SmtSeq`: the field SmtValue of cons
- `SmtValue`: the field native_Real of Real
-/

/-- The constructor of the store for a user operator. -/
def uop : Eo.UserOp → schema.Constructor
  | Eo.UserOp.Int => schema.Constructor.eo_Int
  | Eo.UserOp.Real => schema.Constructor.eo_Real
  | Eo.UserOp.BitVec => schema.Constructor.eo_BitVec
  | Eo.UserOp.Char => schema.Constructor.eo_Char
  | Eo.UserOp.Seq => schema.Constructor.eo_Seq
  | Eo.UserOp.not => schema.Constructor.eo_not
  | Eo.UserOp.and => schema.Constructor.eo_and
  | Eo.UserOp.imp => schema.Constructor.eo__3d_3e
  | Eo.UserOp.eq => schema.Constructor.eo__3d

mutual
/-- The tree of the store that a `Datatype` is stored as. -/
def enc_Datatype : Eo.Datatype → Tree
  | Eo.Datatype.null => Tree.node schema.Constructor.eo__24emb_5fedt_2enull []
  | Eo.Datatype.sum x0 x1 => Tree.node schema.Constructor.eo__24emb_5fedt_2esum [(enc_DatatypeCons x0), (enc_Datatype x1)]
/-- The tree of the store that a `DatatypeCons` is stored as. -/
def enc_DatatypeCons : Eo.DatatypeCons → Tree
  | Eo.DatatypeCons.unit => Tree.node schema.Constructor.eo__24emb_5fedtc_2eunit []
  | Eo.DatatypeCons.cons x0 x1 => Tree.node schema.Constructor.eo__24emb_5fedtc_2econs [(enc_Term x0), (enc_DatatypeCons x1)]
/-- The tree of the store that a `DatatypeDecl` is stored as. -/
def enc_DatatypeDecl : Eo.DatatypeDecl → Tree
  | Eo.DatatypeDecl.nil => Tree.node schema.Constructor.eo__24emb_5fedd_2enil []
  | Eo.DatatypeDecl.cons x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fedd_2econs [(Tree.encStr x0), (enc_Datatype x1), (enc_DatatypeDecl x2)]
/-- The tree of the store that a `Term` is stored as. -/
def enc_Term : Eo.Term → Tree
  | Eo.Term.UOp x0 => Tree.node (uop x0) []
  | Eo.Term.__eo_List => Tree.node schema.Constructor.eo__24eo_5fList []
  | Eo.Term.__eo_List_nil => Tree.node schema.Constructor.eo__24eo_5fList_5fnil []
  | Eo.Term.__eo_List_cons => Tree.node schema.Constructor.eo__24eo_5fList_5fcons []
  | Eo.Term.Bool => Tree.node schema.Constructor.eo__24emb_5fBool []
  | Eo.Term.Boolean x0 => Tree.lit (lit.Lit.Boolean x0)
  | Eo.Term.Numeral x0 => Tree.lit (lit.Lit.Numeral (num.Integer.ofInt x0))
  | Eo.Term.Rational x0 => Tree.lit (lit.Lit.Rational (num.Rational.ofRat x0))
  | Eo.Term.String x0 => Tree.lit (lit.Lit.Str (Tree.strOf x0))
  | Eo.Term.Binary x0 x1 => Tree.lit (lit.Lit.Binary (Tree.bvOf x0 x1))
  | Eo.Term.Type => Tree.node schema.Constructor.eo__24emb_5fType []
  | Eo.Term.Stuck => Tree.stuck
  | Eo.Term.Apply x0 x1 => Tree.apply (enc_Term x0) (enc_Term x1)
  | Eo.Term.FunType => Tree.node schema.Constructor.eo__24emb_5fFunType []
  | Eo.Term.Var x0 x1 => Tree.node schema.Constructor.eo__24emb_5fVar [(enc_Term x0), (enc_Term x1)]
  | Eo.Term.DatatypeType x0 x1 => Tree.node schema.Constructor.eo__24emb_5fDatatypeType [(Tree.encStr x0), (enc_DatatypeDecl x1)]
  | Eo.Term.DatatypeTypeRef x0 => Tree.node schema.Constructor.eo__24emb_5fDatatypeTypeRef [(Tree.encStr x0)]
  | Eo.Term.DtcAppType x0 x1 => Tree.node schema.Constructor.eo__24emb_5fDtcAppType [(enc_Term x0), (enc_Term x1)]
  | Eo.Term.DtCons x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fDtCons [(Tree.encStr x0), (enc_DatatypeDecl x1), (Tree.encNat x2)]
  | Eo.Term.DtSel x0 x1 x2 x3 => Tree.node schema.Constructor.eo__24emb_5fDtSel [(Tree.encStr x0), (enc_DatatypeDecl x1), (Tree.encNat x2), (Tree.encNat x3)]
  | Eo.Term.USort x0 => Tree.node schema.Constructor.eo__24emb_5fUSort [(Tree.encNat x0)]
  | Eo.Term.UConst x0 x1 => Tree.node schema.Constructor.eo__24emb_5fUConst [(Tree.encNat x0), (enc_Term x1)]
end

mutual
/-- The `Datatype` that a tree stands for. -/
def dec_Datatype : Tree → Option Eo.Datatype
  | Tree.node schema.Constructor.eo__24emb_5fedt_2enull [] => some Eo.Datatype.null
  | Tree.node schema.Constructor.eo__24emb_5fedt_2esum [t0, t1] => do
    let x0 ← dec_DatatypeCons t0
    let x1 ← dec_Datatype t1
    some (Eo.Datatype.sum x0 x1)
  | _ => none
/-- The `DatatypeCons` that a tree stands for. -/
def dec_DatatypeCons : Tree → Option Eo.DatatypeCons
  | Tree.node schema.Constructor.eo__24emb_5fedtc_2eunit [] => some Eo.DatatypeCons.unit
  | Tree.node schema.Constructor.eo__24emb_5fedtc_2econs [t0, t1] => do
    let x0 ← dec_Term t0
    let x1 ← dec_DatatypeCons t1
    some (Eo.DatatypeCons.cons x0 x1)
  | _ => none
/-- The `DatatypeDecl` that a tree stands for. -/
def dec_DatatypeDecl : Tree → Option Eo.DatatypeDecl
  | Tree.node schema.Constructor.eo__24emb_5fedd_2enil [] => some Eo.DatatypeDecl.nil
  | Tree.node schema.Constructor.eo__24emb_5fedd_2econs [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_Datatype t1
    let x2 ← dec_DatatypeDecl t2
    some (Eo.DatatypeDecl.cons x0 x1 x2)
  | _ => none
/-- The `Term` that a tree stands for. -/
def dec_Term : Tree → Option Eo.Term
  | Tree.node schema.Constructor.eo_Int [] => some (Eo.Term.UOp Eo.UserOp.Int)
  | Tree.node schema.Constructor.eo_Real [] => some (Eo.Term.UOp Eo.UserOp.Real)
  | Tree.node schema.Constructor.eo_BitVec [] => some (Eo.Term.UOp Eo.UserOp.BitVec)
  | Tree.node schema.Constructor.eo_Char [] => some (Eo.Term.UOp Eo.UserOp.Char)
  | Tree.node schema.Constructor.eo_Seq [] => some (Eo.Term.UOp Eo.UserOp.Seq)
  | Tree.node schema.Constructor.eo_not [] => some (Eo.Term.UOp Eo.UserOp.not)
  | Tree.node schema.Constructor.eo_and [] => some (Eo.Term.UOp Eo.UserOp.and)
  | Tree.node schema.Constructor.eo__3d_3e [] => some (Eo.Term.UOp Eo.UserOp.imp)
  | Tree.node schema.Constructor.eo__3d [] => some (Eo.Term.UOp Eo.UserOp.eq)
  | Tree.node schema.Constructor.eo__24eo_5fList [] => some Eo.Term.__eo_List
  | Tree.node schema.Constructor.eo__24eo_5fList_5fnil [] => some Eo.Term.__eo_List_nil
  | Tree.node schema.Constructor.eo__24eo_5fList_5fcons [] => some Eo.Term.__eo_List_cons
  | Tree.node schema.Constructor.eo__24emb_5fBool [] => some Eo.Term.Bool
  | Tree.lit (lit.Lit.Boolean b) => some (Eo.Term.Boolean b)
  | Tree.lit (lit.Lit.Numeral i) => some (Eo.Term.Numeral i.toInt)
  | Tree.lit (lit.Lit.Rational r) => some (Eo.Term.Rational r.toRat)
  | Tree.lit (lit.Lit.Str v) => some (Eo.Term.String (Tree.strTo v))
  | Tree.lit (lit.Lit.Binary v) => some (Eo.Term.Binary (Tree.bvW v) (Tree.bvV v))
  | Tree.node schema.Constructor.eo__24emb_5fType [] => some Eo.Term.Type
  | Tree.stuck => some Eo.Term.Stuck
  | Tree.apply t0 t1 => do
    let x0 ← dec_Term t0
    let x1 ← dec_Term t1
    some (Eo.Term.Apply x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fFunType [] => some Eo.Term.FunType
  | Tree.node schema.Constructor.eo__24emb_5fVar [t0, t1] => do
    let x0 ← dec_Term t0
    let x1 ← dec_Term t1
    some (Eo.Term.Var x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fDatatypeType [t0, t1] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_DatatypeDecl t1
    some (Eo.Term.DatatypeType x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fDatatypeTypeRef [t0] => do
    let x0 ← Tree.decStr t0
    some (Eo.Term.DatatypeTypeRef x0)
  | Tree.node schema.Constructor.eo__24emb_5fDtcAppType [t0, t1] => do
    let x0 ← dec_Term t0
    let x1 ← dec_Term t1
    some (Eo.Term.DtcAppType x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fDtCons [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_DatatypeDecl t1
    let x2 ← Tree.decNat t2
    some (Eo.Term.DtCons x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fDtSel [t0, t1, t2, t3] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_DatatypeDecl t1
    let x2 ← Tree.decNat t2
    let x3 ← Tree.decNat t3
    some (Eo.Term.DtSel x0 x1 x2 x3)
  | Tree.node schema.Constructor.eo__24emb_5fUSort [t0] => do
    let x0 ← Tree.decNat t0
    some (Eo.Term.USort x0)
  | Tree.node schema.Constructor.eo__24emb_5fUConst [t0, t1] => do
    let x0 ← Tree.decNat t0
    let x1 ← dec_Term t1
    some (Eo.Term.UConst x0 x1)
  | _ => none
end

mutual
/-- A `Datatype` that the store can hold: its natives fit the runtime's. -/
def emb_Datatype : Eo.Datatype → Prop
  | Eo.Datatype.null => True
  | Eo.Datatype.sum x0 x1 => emb_DatatypeCons x0 ∧ emb_Datatype x1
/-- A `DatatypeCons` that the store can hold: its natives fit the runtime's. -/
def emb_DatatypeCons : Eo.DatatypeCons → Prop
  | Eo.DatatypeCons.unit => True
  | Eo.DatatypeCons.cons x0 x1 => emb_Term x0 ∧ emb_DatatypeCons x1
/-- A `DatatypeDecl` that the store can hold: its natives fit the runtime's. -/
def emb_DatatypeDecl : Eo.DatatypeDecl → Prop
  | Eo.DatatypeDecl.nil => True
  | Eo.DatatypeDecl.cons x0 x1 x2 => Tree.okStr x0 ∧ emb_Datatype x1 ∧ emb_DatatypeDecl x2
/-- A `Term` that the store can hold: its natives fit the runtime's. -/
def emb_Term : Eo.Term → Prop
  | Eo.Term.UOp x0 => True
  | Eo.Term.__eo_List => True
  | Eo.Term.__eo_List_nil => True
  | Eo.Term.__eo_List_cons => True
  | Eo.Term.Bool => True
  | Eo.Term.Boolean x0 => True
  | Eo.Term.Numeral x0 => True
  | Eo.Term.Rational x0 => True
  | Eo.Term.String x0 => Tree.okStr x0
  | Eo.Term.Binary x0 x1 => Tree.okBv x0 x1
  | Eo.Term.Type => True
  | Eo.Term.Stuck => True
  | Eo.Term.Apply x0 x1 => emb_Term x0 ∧ emb_Term x1
  | Eo.Term.FunType => True
  | Eo.Term.Var x0 x1 => emb_Term x0 ∧ emb_Term x1
  | Eo.Term.DatatypeType x0 x1 => Tree.okStr x0 ∧ emb_DatatypeDecl x1
  | Eo.Term.DatatypeTypeRef x0 => Tree.okStr x0
  | Eo.Term.DtcAppType x0 x1 => emb_Term x0 ∧ emb_Term x1
  | Eo.Term.DtCons x0 x1 x2 => Tree.okStr x0 ∧ emb_DatatypeDecl x1 ∧ Tree.okNat x2
  | Eo.Term.DtSel x0 x1 x2 x3 => Tree.okStr x0 ∧ emb_DatatypeDecl x1 ∧ Tree.okNat x2 ∧ Tree.okNat x3
  | Eo.Term.USort x0 => Tree.okNat x0
  | Eo.Term.UConst x0 x1 => Tree.okNat x0 ∧ emb_Term x1
end

mutual
theorem dec_enc_Datatype : (x : Eo.Datatype) → emb_Datatype x → dec_Datatype (enc_Datatype x) = some x
  | Eo.Datatype.null, h => by
    simp only [enc_Datatype]
    unfold dec_Datatype
    rfl
  | Eo.Datatype.sum x0 x1, h => by
    simp only [emb_Datatype] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_Datatype]
    unfold dec_Datatype
    simp only [Option.bind_eq_bind, dec_enc_DatatypeCons x0 h0, dec_enc_Datatype x1 h1, Option.bind_some]
theorem dec_enc_DatatypeCons : (x : Eo.DatatypeCons) → emb_DatatypeCons x → dec_DatatypeCons (enc_DatatypeCons x) = some x
  | Eo.DatatypeCons.unit, h => by
    simp only [enc_DatatypeCons]
    unfold dec_DatatypeCons
    rfl
  | Eo.DatatypeCons.cons x0 x1, h => by
    simp only [emb_DatatypeCons] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_DatatypeCons]
    unfold dec_DatatypeCons
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, dec_enc_DatatypeCons x1 h1, Option.bind_some]
theorem dec_enc_DatatypeDecl : (x : Eo.DatatypeDecl) → emb_DatatypeDecl x → dec_DatatypeDecl (enc_DatatypeDecl x) = some x
  | Eo.DatatypeDecl.nil, h => by
    simp only [enc_DatatypeDecl]
    unfold dec_DatatypeDecl
    rfl
  | Eo.DatatypeDecl.cons x0 x1 x2, h => by
    simp only [emb_DatatypeDecl] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_DatatypeDecl]
    unfold dec_DatatypeDecl
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_Datatype x1 h1, dec_enc_DatatypeDecl x2 h2, Option.bind_some]
theorem dec_enc_Term : (x : Eo.Term) → emb_Term x → dec_Term (enc_Term x) = some x
  | Eo.Term.UOp x0, h => by
    cases x0 <;> (simp only [enc_Term, uop]; unfold dec_Term; rfl)
  | Eo.Term.__eo_List, h => by
    simp only [enc_Term]
    unfold dec_Term
    rfl
  | Eo.Term.__eo_List_nil, h => by
    simp only [enc_Term]
    unfold dec_Term
    rfl
  | Eo.Term.__eo_List_cons, h => by
    simp only [enc_Term]
    unfold dec_Term
    rfl
  | Eo.Term.Bool, h => by
    simp only [enc_Term]
    unfold dec_Term
    rfl
  | Eo.Term.Boolean x0, h => by
    simp [enc_Term, dec_Term]
  | Eo.Term.Numeral x0, h => by
    simp [enc_Term, dec_Term, num.Integer.toInt_ofInt]
  | Eo.Term.Rational x0, h => by
    simp [enc_Term, dec_Term, num.Rational.toRat_ofRat]
  | Eo.Term.String x0, h => by
    simp [enc_Term, dec_Term, Tree.strTo_strOf x0 h]
  | Eo.Term.Binary x0 x1, h => by
    simp [enc_Term, dec_Term, Tree.bvW_bvOf x0 x1 h, Tree.bvV_bvOf x0 x1 h]
  | Eo.Term.Type, h => by
    simp only [enc_Term]
    unfold dec_Term
    rfl
  | Eo.Term.Stuck, h => by
    simp [enc_Term, dec_Term]
  | Eo.Term.Apply x0 x1, h => by
    simp only [emb_Term] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_Term, dec_Term, dec_enc_Term x0 h0, dec_enc_Term x1 h1]
  | Eo.Term.FunType, h => by
    simp only [enc_Term]
    unfold dec_Term
    rfl
  | Eo.Term.Var x0 x1, h => by
    simp only [emb_Term] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, dec_enc_Term x1 h1, Option.bind_some]
  | Eo.Term.DatatypeType x0 x1, h => by
    simp only [emb_Term] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_DatatypeDecl x1 h1, Option.bind_some]
  | Eo.Term.DatatypeTypeRef x0, h => by
    simp only [emb_Term] at h
    have h0 := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, Option.bind_some]
  | Eo.Term.DtcAppType x0 x1, h => by
    simp only [emb_Term] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, dec_enc_Term x1 h1, Option.bind_some]
  | Eo.Term.DtCons x0 x1 x2, h => by
    simp only [emb_Term] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_DatatypeDecl x1 h1, Tree.dec_encNat x2 h2, Option.bind_some]
  | Eo.Term.DtSel x0 x1 x2 x3, h => by
    simp only [emb_Term] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_DatatypeDecl x1 h1, Tree.dec_encNat x2 h2, Tree.dec_encNat x3 h3, Option.bind_some]
  | Eo.Term.USort x0, h => by
    simp only [emb_Term] at h
    have h0 := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, Tree.dec_encNat x0 h0, Option.bind_some]
  | Eo.Term.UConst x0 x1, h => by
    simp only [emb_Term] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_Term]
    unfold dec_Term
    simp only [Option.bind_eq_bind, Tree.dec_encNat x0 h0, dec_enc_Term x1 h1, Option.bind_some]
end

theorem inv_Datatype_null {x : Eo.Datatype} {ts : List Tree}
    (h : enc_Datatype x = Tree.node schema.Constructor.eo__24emb_5fedt_2enull ts) (he : emb_Datatype x) :
    x = Eo.Datatype.null ∧ ts = [] := by
  have hd := dec_enc_Datatype x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_Datatype at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_Datatype at hd
    cases hd

theorem inv_Datatype_sum {x : Eo.Datatype} {ts : List Tree}
    (h : enc_Datatype x = Tree.node schema.Constructor.eo__24emb_5fedt_2esum ts) (he : emb_Datatype x) :
    ∃ x0 x1, x = Eo.Datatype.sum x0 x1 ∧ ts = [(enc_DatatypeCons x0), (enc_Datatype x1)] := by
  have hd := dec_enc_Datatype x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_Datatype at hd
    cases hd
  · unfold dec_Datatype at hd
    cases hd
  · unfold dec_Datatype at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_Datatype, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Datatype at hd
    cases hd

theorem inv_DatatypeCons_unit {x : Eo.DatatypeCons} {ts : List Tree}
    (h : enc_DatatypeCons x = Tree.node schema.Constructor.eo__24emb_5fedtc_2eunit ts) (he : emb_DatatypeCons x) :
    x = Eo.DatatypeCons.unit ∧ ts = [] := by
  have hd := dec_enc_DatatypeCons x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_DatatypeCons at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_DatatypeCons at hd
    cases hd

theorem inv_DatatypeCons_cons {x : Eo.DatatypeCons} {ts : List Tree}
    (h : enc_DatatypeCons x = Tree.node schema.Constructor.eo__24emb_5fedtc_2econs ts) (he : emb_DatatypeCons x) :
    ∃ x0 x1, x = Eo.DatatypeCons.cons x0 x1 ∧ ts = [(enc_Term x0), (enc_DatatypeCons x1)] := by
  have hd := dec_enc_DatatypeCons x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_DatatypeCons at hd
    cases hd
  · unfold dec_DatatypeCons at hd
    cases hd
  · unfold dec_DatatypeCons at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_DatatypeCons, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_DatatypeCons at hd
    cases hd

theorem inv_DatatypeDecl_nil {x : Eo.DatatypeDecl} {ts : List Tree}
    (h : enc_DatatypeDecl x = Tree.node schema.Constructor.eo__24emb_5fedd_2enil ts) (he : emb_DatatypeDecl x) :
    x = Eo.DatatypeDecl.nil ∧ ts = [] := by
  have hd := dec_enc_DatatypeDecl x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_DatatypeDecl at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_DatatypeDecl at hd
    cases hd

theorem inv_DatatypeDecl_cons {x : Eo.DatatypeDecl} {ts : List Tree}
    (h : enc_DatatypeDecl x = Tree.node schema.Constructor.eo__24emb_5fedd_2econs ts) (he : emb_DatatypeDecl x) :
    ∃ x0 x1 x2, x = Eo.DatatypeDecl.cons x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_Datatype x1), (enc_DatatypeDecl x2)] := by
  have hd := dec_enc_DatatypeDecl x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_DatatypeDecl at hd
    cases hd
  · unfold dec_DatatypeDecl at hd
    cases hd
  · unfold dec_DatatypeDecl at hd
    cases hd
  · unfold dec_DatatypeDecl at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_DatatypeDecl, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_DatatypeDecl at hd
    cases hd

theorem inv_Term___eo_List {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24eo_5fList ts) (he : emb_Term x) :
    x = Eo.Term.__eo_List ∧ ts = [] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_Term at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term___eo_List_nil {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24eo_5fList_5fnil ts) (he : emb_Term x) :
    x = Eo.Term.__eo_List_nil ∧ ts = [] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_Term at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term___eo_List_cons {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24eo_5fList_5fcons ts) (he : emb_Term x) :
    x = Eo.Term.__eo_List_cons ∧ ts = [] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_Term at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_Bool {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fBool ts) (he : emb_Term x) :
    x = Eo.Term.Bool ∧ ts = [] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_Term at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_Type {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fType ts) (he : emb_Term x) :
    x = Eo.Term.Type ∧ ts = [] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_Term at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_Stuck {x : Eo.Term} (h : enc_Term x = Tree.stuck) : x = Eo.Term.Stuck := by
  cases x <;> simp_all [enc_Term]

theorem inv_Term_Apply {x : Eo.Term} {a b : Tree} (h : enc_Term x = Tree.apply a b) :
    ∃ x0 x1, x = Eo.Term.Apply x0 x1 ∧ a = (enc_Term x0) ∧ b = (enc_Term x1) := by
  cases x <;> simp_all [enc_Term]

theorem inv_Term_FunType {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fFunType ts) (he : emb_Term x) :
    x = Eo.Term.FunType ∧ ts = [] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_Term at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_Var {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fVar ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.Var x0 x1 ∧ ts = [(enc_Term x0), (enc_Term x1)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_DatatypeType {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fDatatypeType ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.DatatypeType x0 x1 ∧ ts = [(Tree.encStr x0), (enc_DatatypeDecl x1)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_DatatypeTypeRef {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fDatatypeTypeRef ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.DatatypeTypeRef x0 ∧ ts = [(Tree.encStr x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_DtcAppType {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fDtcAppType ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.DtcAppType x0 x1 ∧ ts = [(enc_Term x0), (enc_Term x1)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_DtCons {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fDtCons ts) (he : emb_Term x) :
    ∃ x0 x1 x2, x = Eo.Term.DtCons x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_DatatypeDecl x1), (Tree.encNat x2)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_DtSel {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fDtSel ts) (he : emb_Term x) :
    ∃ x0 x1 x2 x3, x = Eo.Term.DtSel x0 x1 x2 x3 ∧ ts = [(Tree.encStr x0), (enc_DatatypeDecl x1), (Tree.encNat x2), (Tree.encNat x3)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨_, _⟩⟩⟩⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, x3, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_USort {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fUSort ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.USort x0 ∧ ts = [(Tree.encNat x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UConst {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__24emb_5fUConst ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.UConst x0 x1 ∧ ts = [(Tree.encNat x0), (enc_Term x1)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_Term, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_lit {x : Eo.Term} {l : lit.Lit} (h : enc_Term x = Tree.lit l) :
    (∃ x0, x = Eo.Term.Boolean x0 ∧ l = lit.Lit.Boolean x0) ∨
      (∃ x0, x = Eo.Term.Numeral x0 ∧ l = lit.Lit.Numeral (num.Integer.ofInt x0)) ∨
      (∃ x0, x = Eo.Term.Rational x0 ∧ l = lit.Lit.Rational (num.Rational.ofRat x0)) ∨
      (∃ x0, x = Eo.Term.String x0 ∧ l = lit.Lit.Str (Tree.strOf x0)) ∨
      (∃ x0 x1, x = Eo.Term.Binary x0 x1 ∧ l = lit.Lit.Binary (Tree.bvOf x0 x1)) := by
  cases x <;> simp_all [enc_Term]

theorem enc_Datatype_node {x : Eo.Datatype} {c : schema.Constructor} {ts : List Tree}
    (h : enc_Datatype x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «null» =>
    simp only [enc_Datatype, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sum» =>
    simp only [enc_Datatype, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

theorem enc_DatatypeCons_node {x : Eo.DatatypeCons} {c : schema.Constructor} {ts : List Tree}
    (h : enc_DatatypeCons x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «unit» =>
    simp only [enc_DatatypeCons, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_DatatypeCons, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

theorem enc_DatatypeDecl_node {x : Eo.DatatypeDecl} {c : schema.Constructor} {ts : List Tree}
    (h : enc_DatatypeDecl x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «nil» =>
    simp only [enc_DatatypeDecl, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_DatatypeDecl, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

theorem enc_Term_node {x : Eo.Term} {c : schema.Constructor} {ts : List Tree}
    (h : enc_Term x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «UOp» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rename_i op
    cases op <;> exact Or.inl rfl
  case «__eo_List» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «__eo_List_nil» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «__eo_List_cons» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Bool» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Boolean» =>
    simp [enc_Term] at h
  case «Numeral» =>
    simp [enc_Term] at h
  case «Rational» =>
    simp [enc_Term] at h
  case «String» =>
    simp [enc_Term] at h
  case «Binary» =>
    simp [enc_Term] at h
  case «Type» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Stuck» =>
    simp [enc_Term] at h
  case «Apply» =>
    simp [enc_Term] at h
  case «FunType» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Var» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inr rfl
  case «DatatypeType» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DatatypeTypeRef» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DtcAppType» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DtCons» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DtSel» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «USort» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «UConst» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.Datatype := ⟨enc_Datatype, dec_Datatype, emb_Datatype, dec_enc_Datatype⟩

@[simp] theorem embedded_enc_Datatype (x : Eo.Datatype) : Embedded.enc x = enc_Datatype x := rfl
@[simp] theorem embedded_emb_Datatype (x : Eo.Datatype) : Embedded.emb x = emb_Datatype x := rfl

instance : Embedded Eo.DatatypeCons := ⟨enc_DatatypeCons, dec_DatatypeCons, emb_DatatypeCons, dec_enc_DatatypeCons⟩

@[simp] theorem embedded_enc_DatatypeCons (x : Eo.DatatypeCons) : Embedded.enc x = enc_DatatypeCons x := rfl
@[simp] theorem embedded_emb_DatatypeCons (x : Eo.DatatypeCons) : Embedded.emb x = emb_DatatypeCons x := rfl

instance : Embedded Eo.DatatypeDecl := ⟨enc_DatatypeDecl, dec_DatatypeDecl, emb_DatatypeDecl, dec_enc_DatatypeDecl⟩

@[simp] theorem embedded_enc_DatatypeDecl (x : Eo.DatatypeDecl) : Embedded.enc x = enc_DatatypeDecl x := rfl
@[simp] theorem embedded_emb_DatatypeDecl (x : Eo.DatatypeDecl) : Embedded.emb x = emb_DatatypeDecl x := rfl

instance : Embedded Eo.Term := ⟨enc_Term, dec_Term, emb_Term, dec_enc_Term⟩

@[simp] theorem embedded_enc_Term (x : Eo.Term) : Embedded.enc x = enc_Term x := rfl
@[simp] theorem embedded_emb_Term (x : Eo.Term) : Embedded.emb x = emb_Term x := rfl

mutual
/-- The tree of the store that a `CArgList` is stored as. -/
def enc_CArgList : Eo.CArgList → Tree
  | Eo.CArgList.nil => Tree.node schema.Constructor.eo__24emb_5fal_2enil []
  | Eo.CArgList.cons x0 x1 => Tree.node schema.Constructor.eo__24emb_5fal_2econs [(enc_Term x0), (enc_CArgList x1)]
end

mutual
/-- The `CArgList` that a tree stands for. -/
def dec_CArgList : Tree → Option Eo.CArgList
  | Tree.node schema.Constructor.eo__24emb_5fal_2enil [] => some Eo.CArgList.nil
  | Tree.node schema.Constructor.eo__24emb_5fal_2econs [t0, t1] => do
    let x0 ← dec_Term t0
    let x1 ← dec_CArgList t1
    some (Eo.CArgList.cons x0 x1)
  | _ => none
end

mutual
/-- A `CArgList` that the store can hold: its natives fit the runtime's. -/
def emb_CArgList : Eo.CArgList → Prop
  | Eo.CArgList.nil => True
  | Eo.CArgList.cons x0 x1 => emb_Term x0 ∧ emb_CArgList x1
end

mutual
theorem dec_enc_CArgList : (x : Eo.CArgList) → emb_CArgList x → dec_CArgList (enc_CArgList x) = some x
  | Eo.CArgList.nil, h => by
    simp only [enc_CArgList]
    unfold dec_CArgList
    rfl
  | Eo.CArgList.cons x0 x1, h => by
    simp only [emb_CArgList] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_CArgList]
    unfold dec_CArgList
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, dec_enc_CArgList x1 h1, Option.bind_some]
end

theorem inv_CArgList_nil {x : Eo.CArgList} {ts : List Tree}
    (h : enc_CArgList x = Tree.node schema.Constructor.eo__24emb_5fal_2enil ts) (he : emb_CArgList x) :
    x = Eo.CArgList.nil ∧ ts = [] := by
  have hd := dec_enc_CArgList x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CArgList at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CArgList at hd
    cases hd

theorem inv_CArgList_cons {x : Eo.CArgList} {ts : List Tree}
    (h : enc_CArgList x = Tree.node schema.Constructor.eo__24emb_5fal_2econs ts) (he : emb_CArgList x) :
    ∃ x0 x1, x = Eo.CArgList.cons x0 x1 ∧ ts = [(enc_Term x0), (enc_CArgList x1)] := by
  have hd := dec_enc_CArgList x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_CArgList at hd
    cases hd
  · unfold dec_CArgList at hd
    cases hd
  · unfold dec_CArgList at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_CArgList, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_CArgList at hd
    cases hd

theorem enc_CArgList_node {x : Eo.CArgList} {c : schema.Constructor} {ts : List Tree}
    (h : enc_CArgList x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «nil» =>
    simp only [enc_CArgList, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_CArgList, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.CArgList := ⟨enc_CArgList, dec_CArgList, emb_CArgList, dec_enc_CArgList⟩

@[simp] theorem embedded_enc_CArgList (x : Eo.CArgList) : Embedded.enc x = enc_CArgList x := rfl
@[simp] theorem embedded_emb_CArgList (x : Eo.CArgList) : Embedded.emb x = emb_CArgList x := rfl

mutual
/-- The tree of the store that a `CIndexList` is stored as. -/
def enc_CIndexList : Eo.CIndexList → Tree
  | Eo.CIndexList.nil => Tree.node schema.Constructor.eo__24emb_5findl_2enil []
  | Eo.CIndexList.cons x0 x1 => Tree.node schema.Constructor.eo__24emb_5findl_2econs [(Tree.encInt x0), (enc_CIndexList x1)]
end

mutual
/-- The `CIndexList` that a tree stands for. -/
def dec_CIndexList : Tree → Option Eo.CIndexList
  | Tree.node schema.Constructor.eo__24emb_5findl_2enil [] => some Eo.CIndexList.nil
  | Tree.node schema.Constructor.eo__24emb_5findl_2econs [t0, t1] => do
    let x0 ← Tree.decInt t0
    let x1 ← dec_CIndexList t1
    some (Eo.CIndexList.cons x0 x1)
  | _ => none
end

mutual
/-- A `CIndexList` that the store can hold: its natives fit the runtime's. -/
def emb_CIndexList : Eo.CIndexList → Prop
  | Eo.CIndexList.nil => True
  | Eo.CIndexList.cons x0 x1 => Tree.okInt x0 ∧ emb_CIndexList x1
end

mutual
theorem dec_enc_CIndexList : (x : Eo.CIndexList) → emb_CIndexList x → dec_CIndexList (enc_CIndexList x) = some x
  | Eo.CIndexList.nil, h => by
    simp only [enc_CIndexList]
    unfold dec_CIndexList
    rfl
  | Eo.CIndexList.cons x0 x1, h => by
    simp only [emb_CIndexList] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_CIndexList]
    unfold dec_CIndexList
    simp only [Option.bind_eq_bind, Tree.dec_encInt x0 h0, dec_enc_CIndexList x1 h1, Option.bind_some]
end

theorem inv_CIndexList_nil {x : Eo.CIndexList} {ts : List Tree}
    (h : enc_CIndexList x = Tree.node schema.Constructor.eo__24emb_5findl_2enil ts) (he : emb_CIndexList x) :
    x = Eo.CIndexList.nil ∧ ts = [] := by
  have hd := dec_enc_CIndexList x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CIndexList at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CIndexList at hd
    cases hd

theorem inv_CIndexList_cons {x : Eo.CIndexList} {ts : List Tree}
    (h : enc_CIndexList x = Tree.node schema.Constructor.eo__24emb_5findl_2econs ts) (he : emb_CIndexList x) :
    ∃ x0 x1, x = Eo.CIndexList.cons x0 x1 ∧ ts = [(Tree.encInt x0), (enc_CIndexList x1)] := by
  have hd := dec_enc_CIndexList x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_CIndexList at hd
    cases hd
  · unfold dec_CIndexList at hd
    cases hd
  · unfold dec_CIndexList at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_CIndexList, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_CIndexList at hd
    cases hd

theorem enc_CIndexList_node {x : Eo.CIndexList} {c : schema.Constructor} {ts : List Tree}
    (h : enc_CIndexList x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «nil» =>
    simp only [enc_CIndexList, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_CIndexList, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.CIndexList := ⟨enc_CIndexList, dec_CIndexList, emb_CIndexList, dec_enc_CIndexList⟩

@[simp] theorem embedded_enc_CIndexList (x : Eo.CIndexList) : Embedded.enc x = enc_CIndexList x := rfl
@[simp] theorem embedded_emb_CIndexList (x : Eo.CIndexList) : Embedded.emb x = emb_CIndexList x := rfl

mutual
/-- The tree of the store that a `CRule` is stored as. -/
def enc_CRule : Eo.CRule → Tree
  | Eo.CRule.scope => Tree.node schema.Constructor.eo__24emb_5fr_2escope []
  | Eo.CRule.contra => Tree.node schema.Constructor.eo__24emb_5fr_2econtra []
  | Eo.CRule.refl => Tree.node schema.Constructor.eo__24emb_5fr_2erefl []
  | Eo.CRule.symm => Tree.node schema.Constructor.eo__24emb_5fr_2esymm []
  | Eo.CRule.trans => Tree.node schema.Constructor.eo__24emb_5fr_2etrans []
end

mutual
/-- The `CRule` that a tree stands for. -/
def dec_CRule : Tree → Option Eo.CRule
  | Tree.node schema.Constructor.eo__24emb_5fr_2escope [] => some Eo.CRule.scope
  | Tree.node schema.Constructor.eo__24emb_5fr_2econtra [] => some Eo.CRule.contra
  | Tree.node schema.Constructor.eo__24emb_5fr_2erefl [] => some Eo.CRule.refl
  | Tree.node schema.Constructor.eo__24emb_5fr_2esymm [] => some Eo.CRule.symm
  | Tree.node schema.Constructor.eo__24emb_5fr_2etrans [] => some Eo.CRule.trans
  | _ => none
end

mutual
/-- A `CRule` that the store can hold: its natives fit the runtime's. -/
def emb_CRule : Eo.CRule → Prop
  | Eo.CRule.scope => True
  | Eo.CRule.contra => True
  | Eo.CRule.refl => True
  | Eo.CRule.symm => True
  | Eo.CRule.trans => True
end

mutual
theorem dec_enc_CRule : (x : Eo.CRule) → emb_CRule x → dec_CRule (enc_CRule x) = some x
  | Eo.CRule.scope, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.contra, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.refl, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.symm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.trans, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
end

theorem inv_CRule_scope {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2escope ts) (he : emb_CRule x) :
    x = Eo.CRule.scope ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econtra ts) (he : emb_CRule x) :
    x = Eo.CRule.contra ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2erefl ts) (he : emb_CRule x) :
    x = Eo.CRule.refl ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_symm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esymm ts) (he : emb_CRule x) :
    x = Eo.CRule.symm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_trans {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2etrans ts) (he : emb_CRule x) :
    x = Eo.CRule.trans ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem enc_CRule_node {x : Eo.CRule} {c : schema.Constructor} {ts : List Tree}
    (h : enc_CRule x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «scope» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «contra» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «refl» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «symm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «trans» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.CRule := ⟨enc_CRule, dec_CRule, emb_CRule, dec_enc_CRule⟩

@[simp] theorem embedded_enc_CRule (x : Eo.CRule) : Embedded.enc x = enc_CRule x := rfl
@[simp] theorem embedded_emb_CRule (x : Eo.CRule) : Embedded.emb x = emb_CRule x := rfl

mutual
/-- The tree of the store that a `CCmd` is stored as. -/
def enc_CCmd : Eo.CCmd → Tree
  | Eo.CCmd.assume_push x0 => Tree.node schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush [(enc_Term x0)]
  | Eo.CCmd.check_proven x0 => Tree.node schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven [(enc_Term x0)]
  | Eo.CCmd.step x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fcmd_2estep [(enc_CRule x0), (enc_CArgList x1), (enc_CIndexList x2)]
  | Eo.CCmd.step_pop x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fcmd_2estep_5fpop [(enc_CRule x0), (enc_CArgList x1), (enc_CIndexList x2)]
end

mutual
/-- The `CCmd` that a tree stands for. -/
def dec_CCmd : Tree → Option Eo.CCmd
  | Tree.node schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush [t0] => do
    let x0 ← dec_Term t0
    some (Eo.CCmd.assume_push x0)
  | Tree.node schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven [t0] => do
    let x0 ← dec_Term t0
    some (Eo.CCmd.check_proven x0)
  | Tree.node schema.Constructor.eo__24emb_5fcmd_2estep [t0, t1, t2] => do
    let x0 ← dec_CRule t0
    let x1 ← dec_CArgList t1
    let x2 ← dec_CIndexList t2
    some (Eo.CCmd.step x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fcmd_2estep_5fpop [t0, t1, t2] => do
    let x0 ← dec_CRule t0
    let x1 ← dec_CArgList t1
    let x2 ← dec_CIndexList t2
    some (Eo.CCmd.step_pop x0 x1 x2)
  | _ => none
end

mutual
/-- A `CCmd` that the store can hold: its natives fit the runtime's. -/
def emb_CCmd : Eo.CCmd → Prop
  | Eo.CCmd.assume_push x0 => emb_Term x0
  | Eo.CCmd.check_proven x0 => emb_Term x0
  | Eo.CCmd.step x0 x1 x2 => emb_CRule x0 ∧ emb_CArgList x1 ∧ emb_CIndexList x2
  | Eo.CCmd.step_pop x0 x1 x2 => emb_CRule x0 ∧ emb_CArgList x1 ∧ emb_CIndexList x2
end

mutual
theorem dec_enc_CCmd : (x : Eo.CCmd) → emb_CCmd x → dec_CCmd (enc_CCmd x) = some x
  | Eo.CCmd.assume_push x0, h => by
    simp only [emb_CCmd] at h
    have h0 := h
    simp only [enc_CCmd]
    unfold dec_CCmd
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, Option.bind_some]
  | Eo.CCmd.check_proven x0, h => by
    simp only [emb_CCmd] at h
    have h0 := h
    simp only [enc_CCmd]
    unfold dec_CCmd
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, Option.bind_some]
  | Eo.CCmd.step x0 x1 x2, h => by
    simp only [emb_CCmd] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_CCmd]
    unfold dec_CCmd
    simp only [Option.bind_eq_bind, dec_enc_CRule x0 h0, dec_enc_CArgList x1 h1, dec_enc_CIndexList x2 h2, Option.bind_some]
  | Eo.CCmd.step_pop x0 x1 x2, h => by
    simp only [emb_CCmd] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_CCmd]
    unfold dec_CCmd
    simp only [Option.bind_eq_bind, dec_enc_CRule x0 h0, dec_enc_CArgList x1 h1, dec_enc_CIndexList x2 h2, Option.bind_some]
end

theorem inv_CCmd_assume_push {x : Eo.CCmd} {ts : List Tree}
    (h : enc_CCmd x = Tree.node schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush ts) (he : emb_CCmd x) :
    ∃ x0, x = Eo.CCmd.assume_push x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_CCmd x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_CCmd, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_CCmd at hd
    cases hd

theorem inv_CCmd_check_proven {x : Eo.CCmd} {ts : List Tree}
    (h : enc_CCmd x = Tree.node schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven ts) (he : emb_CCmd x) :
    ∃ x0, x = Eo.CCmd.check_proven x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_CCmd x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_CCmd, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_CCmd at hd
    cases hd

theorem inv_CCmd_step {x : Eo.CCmd} {ts : List Tree}
    (h : enc_CCmd x = Tree.node schema.Constructor.eo__24emb_5fcmd_2estep ts) (he : emb_CCmd x) :
    ∃ x0 x1 x2, x = Eo.CCmd.step x0 x1 x2 ∧ ts = [(enc_CRule x0), (enc_CArgList x1), (enc_CIndexList x2)] := by
  have hd := dec_enc_CCmd x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_CCmd, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_CCmd at hd
    cases hd

theorem inv_CCmd_step_pop {x : Eo.CCmd} {ts : List Tree}
    (h : enc_CCmd x = Tree.node schema.Constructor.eo__24emb_5fcmd_2estep_5fpop ts) (he : emb_CCmd x) :
    ∃ x0 x1 x2, x = Eo.CCmd.step_pop x0 x1 x2 ∧ ts = [(enc_CRule x0), (enc_CArgList x1), (enc_CIndexList x2)] := by
  have hd := dec_enc_CCmd x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    cases hd
  · unfold dec_CCmd at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_CCmd, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_CCmd at hd
    cases hd

theorem enc_CCmd_node {x : Eo.CCmd} {c : schema.Constructor} {ts : List Tree}
    (h : enc_CCmd x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «assume_push» =>
    simp only [enc_CCmd, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «check_proven» =>
    simp only [enc_CCmd, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «step» =>
    simp only [enc_CCmd, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «step_pop» =>
    simp only [enc_CCmd, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.CCmd := ⟨enc_CCmd, dec_CCmd, emb_CCmd, dec_enc_CCmd⟩

@[simp] theorem embedded_enc_CCmd (x : Eo.CCmd) : Embedded.enc x = enc_CCmd x := rfl
@[simp] theorem embedded_emb_CCmd (x : Eo.CCmd) : Embedded.emb x = emb_CCmd x := rfl

mutual
/-- The tree of the store that a `CCmdList` is stored as. -/
def enc_CCmdList : Eo.CCmdList → Tree
  | Eo.CCmdList.nil => Tree.node schema.Constructor.eo__24emb_5fcmdl_2enil []
  | Eo.CCmdList.cons x0 x1 => Tree.node schema.Constructor.eo__24emb_5fcmdl_2econs [(enc_CCmd x0), (enc_CCmdList x1)]
end

mutual
/-- The `CCmdList` that a tree stands for. -/
def dec_CCmdList : Tree → Option Eo.CCmdList
  | Tree.node schema.Constructor.eo__24emb_5fcmdl_2enil [] => some Eo.CCmdList.nil
  | Tree.node schema.Constructor.eo__24emb_5fcmdl_2econs [t0, t1] => do
    let x0 ← dec_CCmd t0
    let x1 ← dec_CCmdList t1
    some (Eo.CCmdList.cons x0 x1)
  | _ => none
end

mutual
/-- A `CCmdList` that the store can hold: its natives fit the runtime's. -/
def emb_CCmdList : Eo.CCmdList → Prop
  | Eo.CCmdList.nil => True
  | Eo.CCmdList.cons x0 x1 => emb_CCmd x0 ∧ emb_CCmdList x1
end

mutual
theorem dec_enc_CCmdList : (x : Eo.CCmdList) → emb_CCmdList x → dec_CCmdList (enc_CCmdList x) = some x
  | Eo.CCmdList.nil, h => by
    simp only [enc_CCmdList]
    unfold dec_CCmdList
    rfl
  | Eo.CCmdList.cons x0 x1, h => by
    simp only [emb_CCmdList] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_CCmdList]
    unfold dec_CCmdList
    simp only [Option.bind_eq_bind, dec_enc_CCmd x0 h0, dec_enc_CCmdList x1 h1, Option.bind_some]
end

theorem inv_CCmdList_nil {x : Eo.CCmdList} {ts : List Tree}
    (h : enc_CCmdList x = Tree.node schema.Constructor.eo__24emb_5fcmdl_2enil ts) (he : emb_CCmdList x) :
    x = Eo.CCmdList.nil ∧ ts = [] := by
  have hd := dec_enc_CCmdList x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CCmdList at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CCmdList at hd
    cases hd

theorem inv_CCmdList_cons {x : Eo.CCmdList} {ts : List Tree}
    (h : enc_CCmdList x = Tree.node schema.Constructor.eo__24emb_5fcmdl_2econs ts) (he : emb_CCmdList x) :
    ∃ x0 x1, x = Eo.CCmdList.cons x0 x1 ∧ ts = [(enc_CCmd x0), (enc_CCmdList x1)] := by
  have hd := dec_enc_CCmdList x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_CCmdList at hd
    cases hd
  · unfold dec_CCmdList at hd
    cases hd
  · unfold dec_CCmdList at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_CCmdList, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_CCmdList at hd
    cases hd

theorem enc_CCmdList_node {x : Eo.CCmdList} {c : schema.Constructor} {ts : List Tree}
    (h : enc_CCmdList x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «nil» =>
    simp only [enc_CCmdList, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_CCmdList, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.CCmdList := ⟨enc_CCmdList, dec_CCmdList, emb_CCmdList, dec_enc_CCmdList⟩

@[simp] theorem embedded_enc_CCmdList (x : Eo.CCmdList) : Embedded.enc x = enc_CCmdList x := rfl
@[simp] theorem embedded_emb_CCmdList (x : Eo.CCmdList) : Embedded.emb x = emb_CCmdList x := rfl

mutual
/-- The tree of the store that a `CStateObj` is stored as. -/
def enc_CStateObj : Eo.CStateObj → Tree
  | Eo.CStateObj.assume x0 => Tree.node schema.Constructor.eo__24emb_5fso_2eassume [(enc_Term x0)]
  | Eo.CStateObj.assume_push x0 => Tree.node schema.Constructor.eo__24emb_5fso_2eassume_5fpush [(enc_Term x0)]
  | Eo.CStateObj.proven x0 => Tree.node schema.Constructor.eo__24emb_5fso_2eproven [(enc_Term x0)]
end

mutual
/-- The `CStateObj` that a tree stands for. -/
def dec_CStateObj : Tree → Option Eo.CStateObj
  | Tree.node schema.Constructor.eo__24emb_5fso_2eassume [t0] => do
    let x0 ← dec_Term t0
    some (Eo.CStateObj.assume x0)
  | Tree.node schema.Constructor.eo__24emb_5fso_2eassume_5fpush [t0] => do
    let x0 ← dec_Term t0
    some (Eo.CStateObj.assume_push x0)
  | Tree.node schema.Constructor.eo__24emb_5fso_2eproven [t0] => do
    let x0 ← dec_Term t0
    some (Eo.CStateObj.proven x0)
  | _ => none
end

mutual
/-- A `CStateObj` that the store can hold: its natives fit the runtime's. -/
def emb_CStateObj : Eo.CStateObj → Prop
  | Eo.CStateObj.assume x0 => emb_Term x0
  | Eo.CStateObj.assume_push x0 => emb_Term x0
  | Eo.CStateObj.proven x0 => emb_Term x0
end

mutual
theorem dec_enc_CStateObj : (x : Eo.CStateObj) → emb_CStateObj x → dec_CStateObj (enc_CStateObj x) = some x
  | Eo.CStateObj.assume x0, h => by
    simp only [emb_CStateObj] at h
    have h0 := h
    simp only [enc_CStateObj]
    unfold dec_CStateObj
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, Option.bind_some]
  | Eo.CStateObj.assume_push x0, h => by
    simp only [emb_CStateObj] at h
    have h0 := h
    simp only [enc_CStateObj]
    unfold dec_CStateObj
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, Option.bind_some]
  | Eo.CStateObj.proven x0, h => by
    simp only [emb_CStateObj] at h
    have h0 := h
    simp only [enc_CStateObj]
    unfold dec_CStateObj
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, Option.bind_some]
end

theorem inv_CStateObj_assume {x : Eo.CStateObj} {ts : List Tree}
    (h : enc_CStateObj x = Tree.node schema.Constructor.eo__24emb_5fso_2eassume ts) (he : emb_CStateObj x) :
    ∃ x0, x = Eo.CStateObj.assume x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_CStateObj x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_CStateObj at hd
    cases hd
  · unfold dec_CStateObj at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_CStateObj, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_CStateObj at hd
    cases hd

theorem inv_CStateObj_assume_push {x : Eo.CStateObj} {ts : List Tree}
    (h : enc_CStateObj x = Tree.node schema.Constructor.eo__24emb_5fso_2eassume_5fpush ts) (he : emb_CStateObj x) :
    ∃ x0, x = Eo.CStateObj.assume_push x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_CStateObj x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_CStateObj at hd
    cases hd
  · unfold dec_CStateObj at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_CStateObj, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_CStateObj at hd
    cases hd

theorem inv_CStateObj_proven {x : Eo.CStateObj} {ts : List Tree}
    (h : enc_CStateObj x = Tree.node schema.Constructor.eo__24emb_5fso_2eproven ts) (he : emb_CStateObj x) :
    ∃ x0, x = Eo.CStateObj.proven x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_CStateObj x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_CStateObj at hd
    cases hd
  · unfold dec_CStateObj at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_CStateObj, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_CStateObj at hd
    cases hd

theorem enc_CStateObj_node {x : Eo.CStateObj} {c : schema.Constructor} {ts : List Tree}
    (h : enc_CStateObj x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «assume» =>
    simp only [enc_CStateObj, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «assume_push» =>
    simp only [enc_CStateObj, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «proven» =>
    simp only [enc_CStateObj, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.CStateObj := ⟨enc_CStateObj, dec_CStateObj, emb_CStateObj, dec_enc_CStateObj⟩

@[simp] theorem embedded_enc_CStateObj (x : Eo.CStateObj) : Embedded.enc x = enc_CStateObj x := rfl
@[simp] theorem embedded_emb_CStateObj (x : Eo.CStateObj) : Embedded.emb x = emb_CStateObj x := rfl

mutual
/-- The tree of the store that a `CState` is stored as. -/
def enc_CState : Eo.CState → Tree
  | Eo.CState.nil => Tree.node schema.Constructor.eo__24emb_5fs_2enil []
  | Eo.CState.Stuck => Tree.node schema.Constructor.eo__24emb_5fs_2eStuck []
  | Eo.CState.cons x0 x1 => Tree.node schema.Constructor.eo__24emb_5fs_2econs [(enc_CStateObj x0), (enc_CState x1)]
end

mutual
/-- The `CState` that a tree stands for. -/
def dec_CState : Tree → Option Eo.CState
  | Tree.node schema.Constructor.eo__24emb_5fs_2enil [] => some Eo.CState.nil
  | Tree.node schema.Constructor.eo__24emb_5fs_2eStuck [] => some Eo.CState.Stuck
  | Tree.node schema.Constructor.eo__24emb_5fs_2econs [t0, t1] => do
    let x0 ← dec_CStateObj t0
    let x1 ← dec_CState t1
    some (Eo.CState.cons x0 x1)
  | _ => none
end

mutual
/-- A `CState` that the store can hold: its natives fit the runtime's. -/
def emb_CState : Eo.CState → Prop
  | Eo.CState.nil => True
  | Eo.CState.Stuck => True
  | Eo.CState.cons x0 x1 => emb_CStateObj x0 ∧ emb_CState x1
end

mutual
theorem dec_enc_CState : (x : Eo.CState) → emb_CState x → dec_CState (enc_CState x) = some x
  | Eo.CState.nil, h => by
    simp only [enc_CState]
    unfold dec_CState
    rfl
  | Eo.CState.Stuck, h => by
    simp only [enc_CState]
    unfold dec_CState
    rfl
  | Eo.CState.cons x0 x1, h => by
    simp only [emb_CState] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_CState]
    unfold dec_CState
    simp only [Option.bind_eq_bind, dec_enc_CStateObj x0 h0, dec_enc_CState x1 h1, Option.bind_some]
end

theorem inv_CState_nil {x : Eo.CState} {ts : List Tree}
    (h : enc_CState x = Tree.node schema.Constructor.eo__24emb_5fs_2enil ts) (he : emb_CState x) :
    x = Eo.CState.nil ∧ ts = [] := by
  have hd := dec_enc_CState x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CState at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CState at hd
    cases hd

theorem inv_CState_Stuck {x : Eo.CState} {ts : List Tree}
    (h : enc_CState x = Tree.node schema.Constructor.eo__24emb_5fs_2eStuck ts) (he : emb_CState x) :
    x = Eo.CState.Stuck ∧ ts = [] := by
  have hd := dec_enc_CState x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CState at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CState at hd
    cases hd

theorem inv_CState_cons {x : Eo.CState} {ts : List Tree}
    (h : enc_CState x = Tree.node schema.Constructor.eo__24emb_5fs_2econs ts) (he : emb_CState x) :
    ∃ x0 x1, x = Eo.CState.cons x0 x1 ∧ ts = [(enc_CStateObj x0), (enc_CState x1)] := by
  have hd := dec_enc_CState x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_CState at hd
    cases hd
  · unfold dec_CState at hd
    cases hd
  · unfold dec_CState at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_CState, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_CState at hd
    cases hd

theorem enc_CState_node {x : Eo.CState} {c : schema.Constructor} {ts : List Tree}
    (h : enc_CState x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «nil» =>
    simp only [enc_CState, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Stuck» =>
    simp only [enc_CState, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_CState, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Eo.CState := ⟨enc_CState, dec_CState, emb_CState, dec_enc_CState⟩

@[simp] theorem embedded_enc_CState (x : Eo.CState) : Embedded.enc x = enc_CState x := rfl
@[simp] theorem embedded_emb_CState (x : Eo.CState) : Embedded.emb x = emb_CState x := rfl

mutual
/-- The tree of the store that a `Proof` is stored as. -/
def enc_Proof : Eo.Proof → Tree
  | Eo.Proof.pf x0 => Tree.node schema.Constructor.eo__24eo_5fpf [(enc_Term x0)]
  | Eo.Proof.Stuck => Tree.stuck
end

mutual
/-- The `Proof` that a tree stands for. -/
def dec_Proof : Tree → Option Eo.Proof
  | Tree.node schema.Constructor.eo__24eo_5fpf [t0] => do
    let x0 ← dec_Term t0
    some (Eo.Proof.pf x0)
  | Tree.stuck => some Eo.Proof.Stuck
  | _ => none
end

mutual
/-- A `Proof` that the store can hold: its natives fit the runtime's. -/
def emb_Proof : Eo.Proof → Prop
  | Eo.Proof.pf x0 => emb_Term x0
  | Eo.Proof.Stuck => True
end

mutual
theorem dec_enc_Proof : (x : Eo.Proof) → emb_Proof x → dec_Proof (enc_Proof x) = some x
  | Eo.Proof.pf x0, h => by
    simp only [emb_Proof] at h
    have h0 := h
    simp only [enc_Proof]
    unfold dec_Proof
    simp only [Option.bind_eq_bind, dec_enc_Term x0 h0, Option.bind_some]
  | Eo.Proof.Stuck, h => by
    simp [enc_Proof, dec_Proof]
end

theorem inv_Proof_pf {x : Eo.Proof} {ts : List Tree}
    (h : enc_Proof x = Tree.node schema.Constructor.eo__24eo_5fpf ts) (he : emb_Proof x) :
    ∃ x0, x = Eo.Proof.pf x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Proof x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Proof at hd
    cases hd
  · unfold dec_Proof at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Proof, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Proof at hd
    cases hd

theorem inv_Proof_Stuck {x : Eo.Proof} (h : enc_Proof x = Tree.stuck) : x = Eo.Proof.Stuck := by
  cases x <;> simp_all [enc_Proof]

theorem enc_Proof_node {x : Eo.Proof} {c : schema.Constructor} {ts : List Tree}
    (h : enc_Proof x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «pf» =>
    simp only [enc_Proof, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Stuck» =>
    simp [enc_Proof] at h

instance : Embedded Eo.Proof := ⟨enc_Proof, dec_Proof, emb_Proof, dec_enc_Proof⟩

@[simp] theorem embedded_enc_Proof (x : Eo.Proof) : Embedded.enc x = enc_Proof x := rfl
@[simp] theorem embedded_emb_Proof (x : Eo.Proof) : Embedded.emb x = emb_Proof x := rfl

mutual
/-- The tree of the store that a `SmtDatatype` is stored as. -/
def enc_SmtDatatype : Smtm.SmtDatatype → Tree
  | Smtm.SmtDatatype.null => Tree.node schema.Constructor.eo__24emb_5fdt_2enull []
  | Smtm.SmtDatatype.sum x0 x1 => Tree.node schema.Constructor.eo__24emb_5fdt_2esum [(enc_SmtDatatypeCons x0), (enc_SmtDatatype x1)]
/-- The tree of the store that a `SmtDatatypeCons` is stored as. -/
def enc_SmtDatatypeCons : Smtm.SmtDatatypeCons → Tree
  | Smtm.SmtDatatypeCons.unit => Tree.node schema.Constructor.eo__24emb_5fdtc_2eunit []
  | Smtm.SmtDatatypeCons.cons x0 x1 => Tree.node schema.Constructor.eo__24emb_5fdtc_2econs [(enc_SmtType x0), (enc_SmtDatatypeCons x1)]
/-- The tree of the store that a `SmtDatatypeDecl` is stored as. -/
def enc_SmtDatatypeDecl : Smtm.SmtDatatypeDecl → Tree
  | Smtm.SmtDatatypeDecl.nil => Tree.node schema.Constructor.eo__24emb_5fdd_2enil []
  | Smtm.SmtDatatypeDecl.cons x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fdd_2econs [(Tree.encStr x0), (enc_SmtDatatype x1), (enc_SmtDatatypeDecl x2)]
/-- The tree of the store that a `SmtType` is stored as. -/
def enc_SmtType : Smtm.SmtType → Tree
  | Smtm.SmtType.None => Tree.node schema.Constructor.eo__24emb_5ftsm_2eNone []
  | Smtm.SmtType.Bool => Tree.node schema.Constructor.eo__24emb_5ftsm_2eBool []
  | Smtm.SmtType.Int => Tree.node schema.Constructor.eo__24emb_5ftsm_2eInt []
  | Smtm.SmtType.Real => Tree.node schema.Constructor.eo__24emb_5ftsm_2eReal []
  | Smtm.SmtType.RegLan => Tree.node schema.Constructor.eo__24emb_5ftsm_2eRegLan []
  | Smtm.SmtType.BitVec x0 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eBitVec [(Tree.encNat x0)]
  | Smtm.SmtType.Map x0 x1 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eMap [(enc_SmtType x0), (enc_SmtType x1)]
  | Smtm.SmtType.Set x0 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eSet [(enc_SmtType x0)]
  | Smtm.SmtType.Seq x0 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eSeq [(enc_SmtType x0)]
  | Smtm.SmtType.Char => Tree.node schema.Constructor.eo__24emb_5ftsm_2eChar []
  | Smtm.SmtType.Datatype x0 x1 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eDatatype [(Tree.encStr x0), (enc_SmtDatatypeDecl x1)]
  | Smtm.SmtType.TypeRef x0 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eTypeRef [(Tree.encStr x0)]
  | Smtm.SmtType.USort x0 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eUSort [(Tree.encNat x0)]
  | Smtm.SmtType.FunType x0 x1 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eFunType [(enc_SmtType x0), (enc_SmtType x1)]
  | Smtm.SmtType.DtcAppType x0 x1 => Tree.node schema.Constructor.eo__24emb_5ftsm_2eDtcAppType [(enc_SmtType x0), (enc_SmtType x1)]
end

mutual
/-- The `SmtDatatype` that a tree stands for. -/
def dec_SmtDatatype : Tree → Option Smtm.SmtDatatype
  | Tree.node schema.Constructor.eo__24emb_5fdt_2enull [] => some Smtm.SmtDatatype.null
  | Tree.node schema.Constructor.eo__24emb_5fdt_2esum [t0, t1] => do
    let x0 ← dec_SmtDatatypeCons t0
    let x1 ← dec_SmtDatatype t1
    some (Smtm.SmtDatatype.sum x0 x1)
  | _ => none
/-- The `SmtDatatypeCons` that a tree stands for. -/
def dec_SmtDatatypeCons : Tree → Option Smtm.SmtDatatypeCons
  | Tree.node schema.Constructor.eo__24emb_5fdtc_2eunit [] => some Smtm.SmtDatatypeCons.unit
  | Tree.node schema.Constructor.eo__24emb_5fdtc_2econs [t0, t1] => do
    let x0 ← dec_SmtType t0
    let x1 ← dec_SmtDatatypeCons t1
    some (Smtm.SmtDatatypeCons.cons x0 x1)
  | _ => none
/-- The `SmtDatatypeDecl` that a tree stands for. -/
def dec_SmtDatatypeDecl : Tree → Option Smtm.SmtDatatypeDecl
  | Tree.node schema.Constructor.eo__24emb_5fdd_2enil [] => some Smtm.SmtDatatypeDecl.nil
  | Tree.node schema.Constructor.eo__24emb_5fdd_2econs [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtDatatype t1
    let x2 ← dec_SmtDatatypeDecl t2
    some (Smtm.SmtDatatypeDecl.cons x0 x1 x2)
  | _ => none
/-- The `SmtType` that a tree stands for. -/
def dec_SmtType : Tree → Option Smtm.SmtType
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eNone [] => some Smtm.SmtType.None
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eBool [] => some Smtm.SmtType.Bool
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eInt [] => some Smtm.SmtType.Int
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eReal [] => some Smtm.SmtType.Real
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eRegLan [] => some Smtm.SmtType.RegLan
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eBitVec [t0] => do
    let x0 ← Tree.decNat t0
    some (Smtm.SmtType.BitVec x0)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eMap [t0, t1] => do
    let x0 ← dec_SmtType t0
    let x1 ← dec_SmtType t1
    some (Smtm.SmtType.Map x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eSet [t0] => do
    let x0 ← dec_SmtType t0
    some (Smtm.SmtType.Set x0)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eSeq [t0] => do
    let x0 ← dec_SmtType t0
    some (Smtm.SmtType.Seq x0)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eChar [] => some Smtm.SmtType.Char
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eDatatype [t0, t1] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtDatatypeDecl t1
    some (Smtm.SmtType.Datatype x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eTypeRef [t0] => do
    let x0 ← Tree.decStr t0
    some (Smtm.SmtType.TypeRef x0)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eUSort [t0] => do
    let x0 ← Tree.decNat t0
    some (Smtm.SmtType.USort x0)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eFunType [t0, t1] => do
    let x0 ← dec_SmtType t0
    let x1 ← dec_SmtType t1
    some (Smtm.SmtType.FunType x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5ftsm_2eDtcAppType [t0, t1] => do
    let x0 ← dec_SmtType t0
    let x1 ← dec_SmtType t1
    some (Smtm.SmtType.DtcAppType x0 x1)
  | _ => none
end

mutual
/-- A `SmtDatatype` that the store can hold: its natives fit the runtime's. -/
def emb_SmtDatatype : Smtm.SmtDatatype → Prop
  | Smtm.SmtDatatype.null => True
  | Smtm.SmtDatatype.sum x0 x1 => emb_SmtDatatypeCons x0 ∧ emb_SmtDatatype x1
/-- A `SmtDatatypeCons` that the store can hold: its natives fit the runtime's. -/
def emb_SmtDatatypeCons : Smtm.SmtDatatypeCons → Prop
  | Smtm.SmtDatatypeCons.unit => True
  | Smtm.SmtDatatypeCons.cons x0 x1 => emb_SmtType x0 ∧ emb_SmtDatatypeCons x1
/-- A `SmtDatatypeDecl` that the store can hold: its natives fit the runtime's. -/
def emb_SmtDatatypeDecl : Smtm.SmtDatatypeDecl → Prop
  | Smtm.SmtDatatypeDecl.nil => True
  | Smtm.SmtDatatypeDecl.cons x0 x1 x2 => Tree.okStr x0 ∧ emb_SmtDatatype x1 ∧ emb_SmtDatatypeDecl x2
/-- A `SmtType` that the store can hold: its natives fit the runtime's. -/
def emb_SmtType : Smtm.SmtType → Prop
  | Smtm.SmtType.None => True
  | Smtm.SmtType.Bool => True
  | Smtm.SmtType.Int => True
  | Smtm.SmtType.Real => True
  | Smtm.SmtType.RegLan => True
  | Smtm.SmtType.BitVec x0 => Tree.okNat x0
  | Smtm.SmtType.Map x0 x1 => emb_SmtType x0 ∧ emb_SmtType x1
  | Smtm.SmtType.Set x0 => emb_SmtType x0
  | Smtm.SmtType.Seq x0 => emb_SmtType x0
  | Smtm.SmtType.Char => True
  | Smtm.SmtType.Datatype x0 x1 => Tree.okStr x0 ∧ emb_SmtDatatypeDecl x1
  | Smtm.SmtType.TypeRef x0 => Tree.okStr x0
  | Smtm.SmtType.USort x0 => Tree.okNat x0
  | Smtm.SmtType.FunType x0 x1 => emb_SmtType x0 ∧ emb_SmtType x1
  | Smtm.SmtType.DtcAppType x0 x1 => emb_SmtType x0 ∧ emb_SmtType x1
end

mutual
theorem dec_enc_SmtDatatype : (x : Smtm.SmtDatatype) → emb_SmtDatatype x → dec_SmtDatatype (enc_SmtDatatype x) = some x
  | Smtm.SmtDatatype.null, h => by
    simp only [enc_SmtDatatype]
    unfold dec_SmtDatatype
    rfl
  | Smtm.SmtDatatype.sum x0 x1, h => by
    simp only [emb_SmtDatatype] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtDatatype]
    unfold dec_SmtDatatype
    simp only [Option.bind_eq_bind, dec_enc_SmtDatatypeCons x0 h0, dec_enc_SmtDatatype x1 h1, Option.bind_some]
theorem dec_enc_SmtDatatypeCons : (x : Smtm.SmtDatatypeCons) → emb_SmtDatatypeCons x → dec_SmtDatatypeCons (enc_SmtDatatypeCons x) = some x
  | Smtm.SmtDatatypeCons.unit, h => by
    simp only [enc_SmtDatatypeCons]
    unfold dec_SmtDatatypeCons
    rfl
  | Smtm.SmtDatatypeCons.cons x0 x1, h => by
    simp only [emb_SmtDatatypeCons] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtDatatypeCons]
    unfold dec_SmtDatatypeCons
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, dec_enc_SmtDatatypeCons x1 h1, Option.bind_some]
theorem dec_enc_SmtDatatypeDecl : (x : Smtm.SmtDatatypeDecl) → emb_SmtDatatypeDecl x → dec_SmtDatatypeDecl (enc_SmtDatatypeDecl x) = some x
  | Smtm.SmtDatatypeDecl.nil, h => by
    simp only [enc_SmtDatatypeDecl]
    unfold dec_SmtDatatypeDecl
    rfl
  | Smtm.SmtDatatypeDecl.cons x0 x1 x2, h => by
    simp only [emb_SmtDatatypeDecl] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtDatatypeDecl]
    unfold dec_SmtDatatypeDecl
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtDatatype x1 h1, dec_enc_SmtDatatypeDecl x2 h2, Option.bind_some]
theorem dec_enc_SmtType : (x : Smtm.SmtType) → emb_SmtType x → dec_SmtType (enc_SmtType x) = some x
  | Smtm.SmtType.None, h => by
    simp only [enc_SmtType]
    unfold dec_SmtType
    rfl
  | Smtm.SmtType.Bool, h => by
    simp only [enc_SmtType]
    unfold dec_SmtType
    rfl
  | Smtm.SmtType.Int, h => by
    simp only [enc_SmtType]
    unfold dec_SmtType
    rfl
  | Smtm.SmtType.Real, h => by
    simp only [enc_SmtType]
    unfold dec_SmtType
    rfl
  | Smtm.SmtType.RegLan, h => by
    simp only [enc_SmtType]
    unfold dec_SmtType
    rfl
  | Smtm.SmtType.BitVec x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, Tree.dec_encNat x0 h0, Option.bind_some]
  | Smtm.SmtType.Map x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, dec_enc_SmtType x1 h1, Option.bind_some]
  | Smtm.SmtType.Set x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, Option.bind_some]
  | Smtm.SmtType.Seq x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, Option.bind_some]
  | Smtm.SmtType.Char, h => by
    simp only [enc_SmtType]
    unfold dec_SmtType
    rfl
  | Smtm.SmtType.Datatype x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1, Option.bind_some]
  | Smtm.SmtType.TypeRef x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, Option.bind_some]
  | Smtm.SmtType.USort x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, Tree.dec_encNat x0 h0, Option.bind_some]
  | Smtm.SmtType.FunType x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, dec_enc_SmtType x1 h1, Option.bind_some]
  | Smtm.SmtType.DtcAppType x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtType]
    unfold dec_SmtType
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, dec_enc_SmtType x1 h1, Option.bind_some]
end

theorem inv_SmtDatatype_null {x : Smtm.SmtDatatype} {ts : List Tree}
    (h : enc_SmtDatatype x = Tree.node schema.Constructor.eo__24emb_5fdt_2enull ts) (he : emb_SmtDatatype x) :
    x = Smtm.SmtDatatype.null ∧ ts = [] := by
  have hd := dec_enc_SmtDatatype x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtDatatype at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtDatatype at hd
    cases hd

theorem inv_SmtDatatype_sum {x : Smtm.SmtDatatype} {ts : List Tree}
    (h : enc_SmtDatatype x = Tree.node schema.Constructor.eo__24emb_5fdt_2esum ts) (he : emb_SmtDatatype x) :
    ∃ x0 x1, x = Smtm.SmtDatatype.sum x0 x1 ∧ ts = [(enc_SmtDatatypeCons x0), (enc_SmtDatatype x1)] := by
  have hd := dec_enc_SmtDatatype x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtDatatype at hd
    cases hd
  · unfold dec_SmtDatatype at hd
    cases hd
  · unfold dec_SmtDatatype at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtDatatype, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtDatatype at hd
    cases hd

theorem inv_SmtDatatypeCons_unit {x : Smtm.SmtDatatypeCons} {ts : List Tree}
    (h : enc_SmtDatatypeCons x = Tree.node schema.Constructor.eo__24emb_5fdtc_2eunit ts) (he : emb_SmtDatatypeCons x) :
    x = Smtm.SmtDatatypeCons.unit ∧ ts = [] := by
  have hd := dec_enc_SmtDatatypeCons x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtDatatypeCons at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtDatatypeCons at hd
    cases hd

theorem inv_SmtDatatypeCons_cons {x : Smtm.SmtDatatypeCons} {ts : List Tree}
    (h : enc_SmtDatatypeCons x = Tree.node schema.Constructor.eo__24emb_5fdtc_2econs ts) (he : emb_SmtDatatypeCons x) :
    ∃ x0 x1, x = Smtm.SmtDatatypeCons.cons x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtDatatypeCons x1)] := by
  have hd := dec_enc_SmtDatatypeCons x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtDatatypeCons at hd
    cases hd
  · unfold dec_SmtDatatypeCons at hd
    cases hd
  · unfold dec_SmtDatatypeCons at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtDatatypeCons, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtDatatypeCons at hd
    cases hd

theorem inv_SmtDatatypeDecl_nil {x : Smtm.SmtDatatypeDecl} {ts : List Tree}
    (h : enc_SmtDatatypeDecl x = Tree.node schema.Constructor.eo__24emb_5fdd_2enil ts) (he : emb_SmtDatatypeDecl x) :
    x = Smtm.SmtDatatypeDecl.nil ∧ ts = [] := by
  have hd := dec_enc_SmtDatatypeDecl x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtDatatypeDecl at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtDatatypeDecl at hd
    cases hd

theorem inv_SmtDatatypeDecl_cons {x : Smtm.SmtDatatypeDecl} {ts : List Tree}
    (h : enc_SmtDatatypeDecl x = Tree.node schema.Constructor.eo__24emb_5fdd_2econs ts) (he : emb_SmtDatatypeDecl x) :
    ∃ x0 x1 x2, x = Smtm.SmtDatatypeDecl.cons x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatype x1), (enc_SmtDatatypeDecl x2)] := by
  have hd := dec_enc_SmtDatatypeDecl x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_SmtDatatypeDecl at hd
    cases hd
  · unfold dec_SmtDatatypeDecl at hd
    cases hd
  · unfold dec_SmtDatatypeDecl at hd
    cases hd
  · unfold dec_SmtDatatypeDecl at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_SmtDatatypeDecl, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_SmtDatatypeDecl at hd
    cases hd

theorem inv_SmtType_None {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eNone ts) (he : emb_SmtType x) :
    x = Smtm.SmtType.None ∧ ts = [] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtType at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Bool {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eBool ts) (he : emb_SmtType x) :
    x = Smtm.SmtType.Bool ∧ ts = [] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtType at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Int {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eInt ts) (he : emb_SmtType x) :
    x = Smtm.SmtType.Int ∧ ts = [] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtType at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Real {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eReal ts) (he : emb_SmtType x) :
    x = Smtm.SmtType.Real ∧ ts = [] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtType at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_RegLan {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eRegLan ts) (he : emb_SmtType x) :
    x = Smtm.SmtType.RegLan ∧ ts = [] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtType at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_BitVec {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eBitVec ts) (he : emb_SmtType x) :
    ∃ x0, x = Smtm.SmtType.BitVec x0 ∧ ts = [(Tree.encNat x0)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Map {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eMap ts) (he : emb_SmtType x) :
    ∃ x0 x1, x = Smtm.SmtType.Map x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtType x1)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Set {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eSet ts) (he : emb_SmtType x) :
    ∃ x0, x = Smtm.SmtType.Set x0 ∧ ts = [(enc_SmtType x0)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Seq {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eSeq ts) (he : emb_SmtType x) :
    ∃ x0, x = Smtm.SmtType.Seq x0 ∧ ts = [(enc_SmtType x0)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Char {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eChar ts) (he : emb_SmtType x) :
    x = Smtm.SmtType.Char ∧ ts = [] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtType at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_Datatype {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eDatatype ts) (he : emb_SmtType x) :
    ∃ x0 x1, x = Smtm.SmtType.Datatype x0 x1 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_TypeRef {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eTypeRef ts) (he : emb_SmtType x) :
    ∃ x0, x = Smtm.SmtType.TypeRef x0 ∧ ts = [(Tree.encStr x0)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_USort {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eUSort ts) (he : emb_SmtType x) :
    ∃ x0, x = Smtm.SmtType.USort x0 ∧ ts = [(Tree.encNat x0)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_FunType {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eFunType ts) (he : emb_SmtType x) :
    ∃ x0 x1, x = Smtm.SmtType.FunType x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtType x1)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem inv_SmtType_DtcAppType {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eDtcAppType ts) (he : emb_SmtType x) :
    ∃ x0 x1, x = Smtm.SmtType.DtcAppType x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtType x1)] := by
  have hd := dec_enc_SmtType x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    cases hd
  · unfold dec_SmtType at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtType, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtType at hd
    cases hd

theorem enc_SmtDatatype_node {x : Smtm.SmtDatatype} {c : schema.Constructor} {ts : List Tree}
    (h : enc_SmtDatatype x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «null» =>
    simp only [enc_SmtDatatype, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sum» =>
    simp only [enc_SmtDatatype, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

theorem enc_SmtDatatypeCons_node {x : Smtm.SmtDatatypeCons} {c : schema.Constructor} {ts : List Tree}
    (h : enc_SmtDatatypeCons x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «unit» =>
    simp only [enc_SmtDatatypeCons, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_SmtDatatypeCons, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

theorem enc_SmtDatatypeDecl_node {x : Smtm.SmtDatatypeDecl} {c : schema.Constructor} {ts : List Tree}
    (h : enc_SmtDatatypeDecl x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «nil» =>
    simp only [enc_SmtDatatypeDecl, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_SmtDatatypeDecl, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

theorem enc_SmtType_node {x : Smtm.SmtType} {c : schema.Constructor} {ts : List Tree}
    (h : enc_SmtType x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «None» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Bool» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Int» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Real» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «RegLan» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «BitVec» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Map» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Set» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Seq» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Char» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Datatype» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «TypeRef» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «USort» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «FunType» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DtcAppType» =>
    simp only [enc_SmtType, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Smtm.SmtDatatype := ⟨enc_SmtDatatype, dec_SmtDatatype, emb_SmtDatatype, dec_enc_SmtDatatype⟩

@[simp] theorem embedded_enc_SmtDatatype (x : Smtm.SmtDatatype) : Embedded.enc x = enc_SmtDatatype x := rfl
@[simp] theorem embedded_emb_SmtDatatype (x : Smtm.SmtDatatype) : Embedded.emb x = emb_SmtDatatype x := rfl

instance : Embedded Smtm.SmtDatatypeCons := ⟨enc_SmtDatatypeCons, dec_SmtDatatypeCons, emb_SmtDatatypeCons, dec_enc_SmtDatatypeCons⟩

@[simp] theorem embedded_enc_SmtDatatypeCons (x : Smtm.SmtDatatypeCons) : Embedded.enc x = enc_SmtDatatypeCons x := rfl
@[simp] theorem embedded_emb_SmtDatatypeCons (x : Smtm.SmtDatatypeCons) : Embedded.emb x = emb_SmtDatatypeCons x := rfl

instance : Embedded Smtm.SmtDatatypeDecl := ⟨enc_SmtDatatypeDecl, dec_SmtDatatypeDecl, emb_SmtDatatypeDecl, dec_enc_SmtDatatypeDecl⟩

@[simp] theorem embedded_enc_SmtDatatypeDecl (x : Smtm.SmtDatatypeDecl) : Embedded.enc x = enc_SmtDatatypeDecl x := rfl
@[simp] theorem embedded_emb_SmtDatatypeDecl (x : Smtm.SmtDatatypeDecl) : Embedded.emb x = emb_SmtDatatypeDecl x := rfl

instance : Embedded Smtm.SmtType := ⟨enc_SmtType, dec_SmtType, emb_SmtType, dec_enc_SmtType⟩

@[simp] theorem embedded_enc_SmtType (x : Smtm.SmtType) : Embedded.enc x = enc_SmtType x := rfl
@[simp] theorem embedded_emb_SmtType (x : Smtm.SmtType) : Embedded.emb x = emb_SmtType x := rfl

mutual
/-- The tree of the store that a `SmtTerm` is stored as. -/
def enc_SmtTerm : Smtm.SmtTerm → Tree
  | Smtm.SmtTerm.None => Tree.node schema.Constructor.eo__24emb_5fsm_2eNone []
  | Smtm.SmtTerm.Boolean x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eBoolean [(Tree.encBool x0)]
  | Smtm.SmtTerm.Numeral x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eNumeral [(Tree.encInt x0)]
  | Smtm.SmtTerm.Rational x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eRational [(Tree.encRat x0)]
  | Smtm.SmtTerm.String x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eString [(Tree.encStr x0)]
  | Smtm.SmtTerm.Binary x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eBinary [(Tree.encInt x0), (Tree.encInt x1)]
  | Smtm.SmtTerm.Apply x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eApply [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.Var x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eVar [(Tree.encStr x0), (enc_SmtType x1)]
  | Smtm.SmtTerm.DtCons x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2eDtCons [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2)]
  | Smtm.SmtTerm.DtSel x0 x1 x2 x3 => Tree.node schema.Constructor.eo__24emb_5fsm_2eDtSel [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2), (Tree.encNat x3)]
  | Smtm.SmtTerm.DtTester x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2eDtTester [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2)]
  | Smtm.SmtTerm.UConst x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eUConst [(Tree.encStr x0), (enc_SmtType x1)]
  | Smtm.SmtTerm.not x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2enot [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.and x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eand [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.or x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eor [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.imp x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d_3e [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.eq x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.ite x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2eite [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
end

mutual
/-- The `SmtTerm` that a tree stands for. -/
def dec_SmtTerm : Tree → Option Smtm.SmtTerm
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eNone [] => some Smtm.SmtTerm.None
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eBoolean [t0] => do
    let x0 ← Tree.decBool t0
    some (Smtm.SmtTerm.Boolean x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eNumeral [t0] => do
    let x0 ← Tree.decInt t0
    some (Smtm.SmtTerm.Numeral x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eRational [t0] => do
    let x0 ← Tree.decRat t0
    some (Smtm.SmtTerm.Rational x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eString [t0] => do
    let x0 ← Tree.decStr t0
    some (Smtm.SmtTerm.String x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eBinary [t0, t1] => do
    let x0 ← Tree.decInt t0
    let x1 ← Tree.decInt t1
    some (Smtm.SmtTerm.Binary x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eApply [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.Apply x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eVar [t0, t1] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtType t1
    some (Smtm.SmtTerm.Var x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eDtCons [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtDatatypeDecl t1
    let x2 ← Tree.decNat t2
    some (Smtm.SmtTerm.DtCons x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eDtSel [t0, t1, t2, t3] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtDatatypeDecl t1
    let x2 ← Tree.decNat t2
    let x3 ← Tree.decNat t3
    some (Smtm.SmtTerm.DtSel x0 x1 x2 x3)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eDtTester [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtDatatypeDecl t1
    let x2 ← Tree.decNat t2
    some (Smtm.SmtTerm.DtTester x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eUConst [t0, t1] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtType t1
    some (Smtm.SmtTerm.UConst x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2enot [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.not x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eand [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.and x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eor [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.or x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d_3e [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.imp x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.eq x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eite [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.ite x0 x1 x2)
  | _ => none
end

mutual
/-- A `SmtTerm` that the store can hold: its natives fit the runtime's. -/
def emb_SmtTerm : Smtm.SmtTerm → Prop
  | Smtm.SmtTerm.None => True
  | Smtm.SmtTerm.Boolean x0 => Tree.okBool x0
  | Smtm.SmtTerm.Numeral x0 => Tree.okInt x0
  | Smtm.SmtTerm.Rational x0 => Tree.okRat x0
  | Smtm.SmtTerm.String x0 => Tree.okStr x0
  | Smtm.SmtTerm.Binary x0 x1 => Tree.okInt x0 ∧ Tree.okInt x1
  | Smtm.SmtTerm.Apply x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.Var x0 x1 => Tree.okStr x0 ∧ emb_SmtType x1
  | Smtm.SmtTerm.DtCons x0 x1 x2 => Tree.okStr x0 ∧ emb_SmtDatatypeDecl x1 ∧ Tree.okNat x2
  | Smtm.SmtTerm.DtSel x0 x1 x2 x3 => Tree.okStr x0 ∧ emb_SmtDatatypeDecl x1 ∧ Tree.okNat x2 ∧ Tree.okNat x3
  | Smtm.SmtTerm.DtTester x0 x1 x2 => Tree.okStr x0 ∧ emb_SmtDatatypeDecl x1 ∧ Tree.okNat x2
  | Smtm.SmtTerm.UConst x0 x1 => Tree.okStr x0 ∧ emb_SmtType x1
  | Smtm.SmtTerm.not x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.and x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.or x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.imp x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.eq x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.ite x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
end

mutual
theorem dec_enc_SmtTerm : (x : Smtm.SmtTerm) → emb_SmtTerm x → dec_SmtTerm (enc_SmtTerm x) = some x
  | Smtm.SmtTerm.None, h => by
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    rfl
  | Smtm.SmtTerm.Boolean x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encBool x0 h0, Option.bind_some]
  | Smtm.SmtTerm.Numeral x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encInt x0 h0, Option.bind_some]
  | Smtm.SmtTerm.Rational x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encRat x0 h0, Option.bind_some]
  | Smtm.SmtTerm.String x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, Option.bind_some]
  | Smtm.SmtTerm.Binary x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encInt x0 h0, Tree.dec_encInt x1 h1, Option.bind_some]
  | Smtm.SmtTerm.Apply x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.Var x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, Option.bind_some]
  | Smtm.SmtTerm.DtCons x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1, Tree.dec_encNat x2 h2, Option.bind_some]
  | Smtm.SmtTerm.DtSel x0 x1 x2 x3, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1, Tree.dec_encNat x2 h2, Tree.dec_encNat x3 h3, Option.bind_some]
  | Smtm.SmtTerm.DtTester x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1, Tree.dec_encNat x2 h2, Option.bind_some]
  | Smtm.SmtTerm.UConst x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, Option.bind_some]
  | Smtm.SmtTerm.not x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.and x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.or x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.imp x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.eq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.ite x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
end

theorem inv_SmtTerm_None {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eNone ts) (he : emb_SmtTerm x) :
    x = Smtm.SmtTerm.None ∧ ts = [] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtTerm at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_Boolean {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eBoolean ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.Boolean x0 ∧ ts = [(Tree.encBool x0)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_Numeral {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eNumeral ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.Numeral x0 ∧ ts = [(Tree.encInt x0)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_Rational {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eRational ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.Rational x0 ∧ ts = [(Tree.encRat x0)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_String {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eString ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.String x0 ∧ ts = [(Tree.encStr x0)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_Binary {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eBinary ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.Binary x0 x1 ∧ ts = [(Tree.encInt x0), (Tree.encInt x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_Apply {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eApply ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.Apply x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_Var {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eVar ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.Var x0 x1 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_DtCons {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eDtCons ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.DtCons x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_DtSel {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eDtSel ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2 x3, x = Smtm.SmtTerm.DtSel x0 x1 x2 x3 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2), (Tree.encNat x3)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨_, _⟩⟩⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, x3, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_DtTester {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eDtTester ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.DtTester x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_UConst {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eUConst ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.UConst x0 x1 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_not {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2enot ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.not x0 ∧ ts = [(enc_SmtTerm x0)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_and {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eand ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.and x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_or {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eor ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.or x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_imp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d_3e ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.imp x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_eq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.eq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨_, _⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_ite {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eite ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.ite x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨_, _⟩⟩⟩⟩
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    cases hd
  · unfold dec_SmtTerm at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, rfl⟩ := hd
    simp only [enc_SmtTerm, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem enc_SmtTerm_node {x : Smtm.SmtTerm} {c : schema.Constructor} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «None» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Boolean» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Numeral» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Rational» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «String» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Binary» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Apply» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «Var» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DtCons» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DtSel» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «DtTester» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «UConst» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «and» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «or» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «imp» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «eq» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Smtm.SmtTerm := ⟨enc_SmtTerm, dec_SmtTerm, emb_SmtTerm, dec_enc_SmtTerm⟩

@[simp] theorem embedded_enc_SmtTerm (x : Smtm.SmtTerm) : Embedded.enc x = enc_SmtTerm x := rfl
@[simp] theorem embedded_emb_SmtTerm (x : Smtm.SmtTerm) : Embedded.emb x = emb_SmtTerm x := rfl


end

end pathos_compiled_checker.Embed
