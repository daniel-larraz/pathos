module

public import CpcChecker
public import PathosProofs.Store.Tree
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtTranslate

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
`CpcEmbed.lean`); `CpcChecker` is the Lean of the compiled checker.
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
  | Eo.UserOp._at__at_Pair => schema.Constructor.eo__40_40Pair
  | Eo.UserOp._at__at_pair => schema.Constructor.eo__40_40pair
  | Eo.UserOp._at__at_TypedList => schema.Constructor.eo__40_40TypedList
  | Eo.UserOp._at__at_TypedList_nil => schema.Constructor.eo__40_40TypedList_2enil
  | Eo.UserOp._at__at_TypedList_cons => schema.Constructor.eo__40_40TypedList_2econs
  | Eo.UserOp.ite => schema.Constructor.eo_ite
  | Eo.UserOp.not => schema.Constructor.eo_not
  | Eo.UserOp.or => schema.Constructor.eo_or
  | Eo.UserOp.and => schema.Constructor.eo_and
  | Eo.UserOp.imp => schema.Constructor.eo__3d_3e
  | Eo.UserOp.xor => schema.Constructor.eo_xor
  | Eo.UserOp.eq => schema.Constructor.eo__3d
  | Eo.UserOp.lambda => schema.Constructor.eo_lambda
  | Eo.UserOp.distinct => schema.Constructor.eo_distinct
  | Eo.UserOp._at_purify => schema.Constructor.eo__40purify
  | Eo.UserOp.plus => schema.Constructor.eo__2b
  | Eo.UserOp.neg => schema.Constructor.eo__2d
  | Eo.UserOp.mult => schema.Constructor.eo__2a
  | Eo.UserOp.lt => schema.Constructor.eo__3c
  | Eo.UserOp.leq => schema.Constructor.eo__3c_3d
  | Eo.UserOp.gt => schema.Constructor.eo__3e
  | Eo.UserOp.geq => schema.Constructor.eo__3e_3d
  | Eo.UserOp.to_real => schema.Constructor.eo_to_5freal
  | Eo.UserOp.to_int => schema.Constructor.eo_to_5fint
  | Eo.UserOp.is_int => schema.Constructor.eo_is_5fint
  | Eo.UserOp.abs => schema.Constructor.eo_abs
  | Eo.UserOp.__eoo_neg_2 => schema.Constructor.eo__24eoo_5f_2d_2e2
  | Eo.UserOp.div => schema.Constructor.eo_div
  | Eo.UserOp.mod => schema.Constructor.eo_mod
  | Eo.UserOp.divisible => schema.Constructor.eo_divisible
  | Eo.UserOp.int_pow2 => schema.Constructor.eo_int_2epow2
  | Eo.UserOp.int_log2 => schema.Constructor.eo_int_2elog2
  | Eo.UserOp.int_ispow2 => schema.Constructor.eo_int_2eispow2
  | Eo.UserOp.div_total => schema.Constructor.eo_div_5ftotal
  | Eo.UserOp.mod_total => schema.Constructor.eo_mod_5ftotal
  | Eo.UserOp._at_int_div_by_zero => schema.Constructor.eo__40int_5fdiv_5fby_5fzero
  | Eo.UserOp._at_mod_by_zero => schema.Constructor.eo__40mod_5fby_5fzero
  | Eo.UserOp.Array => schema.Constructor.eo_Array
  | Eo.UserOp.select => schema.Constructor.eo_select
  | Eo.UserOp.store => schema.Constructor.eo_store
  | Eo.UserOp._at_array_deq_diff => schema.Constructor.eo__40array_5fdeq_5fdiff
  | Eo.UserOp._at_bvsize => schema.Constructor.eo__40bvsize
  | Eo.UserOp.concat => schema.Constructor.eo_concat
  | Eo.UserOp.bvnot => schema.Constructor.eo_bvnot
  | Eo.UserOp.bvand => schema.Constructor.eo_bvand
  | Eo.UserOp.bvor => schema.Constructor.eo_bvor
  | Eo.UserOp.bvnand => schema.Constructor.eo_bvnand
  | Eo.UserOp.bvnor => schema.Constructor.eo_bvnor
  | Eo.UserOp.bvxor => schema.Constructor.eo_bvxor
  | Eo.UserOp.bvxnor => schema.Constructor.eo_bvxnor
  | Eo.UserOp.bvcomp => schema.Constructor.eo_bvcomp
  | Eo.UserOp.bvneg => schema.Constructor.eo_bvneg
  | Eo.UserOp.bvadd => schema.Constructor.eo_bvadd
  | Eo.UserOp.bvmul => schema.Constructor.eo_bvmul
  | Eo.UserOp.bvudiv => schema.Constructor.eo_bvudiv
  | Eo.UserOp.bvurem => schema.Constructor.eo_bvurem
  | Eo.UserOp.bvsub => schema.Constructor.eo_bvsub
  | Eo.UserOp.bvsdiv => schema.Constructor.eo_bvsdiv
  | Eo.UserOp.bvsrem => schema.Constructor.eo_bvsrem
  | Eo.UserOp.bvsmod => schema.Constructor.eo_bvsmod
  | Eo.UserOp.bvult => schema.Constructor.eo_bvult
  | Eo.UserOp.bvule => schema.Constructor.eo_bvule
  | Eo.UserOp.bvugt => schema.Constructor.eo_bvugt
  | Eo.UserOp.bvuge => schema.Constructor.eo_bvuge
  | Eo.UserOp.bvslt => schema.Constructor.eo_bvslt
  | Eo.UserOp.bvsle => schema.Constructor.eo_bvsle
  | Eo.UserOp.bvsgt => schema.Constructor.eo_bvsgt
  | Eo.UserOp.bvsge => schema.Constructor.eo_bvsge
  | Eo.UserOp.bvshl => schema.Constructor.eo_bvshl
  | Eo.UserOp.bvlshr => schema.Constructor.eo_bvlshr
  | Eo.UserOp.bvashr => schema.Constructor.eo_bvashr
  | Eo.UserOp.bvite => schema.Constructor.eo_bvite
  | Eo.UserOp.bvuaddo => schema.Constructor.eo_bvuaddo
  | Eo.UserOp.bvnego => schema.Constructor.eo_bvnego
  | Eo.UserOp.bvsaddo => schema.Constructor.eo_bvsaddo
  | Eo.UserOp.bvumulo => schema.Constructor.eo_bvumulo
  | Eo.UserOp.bvsmulo => schema.Constructor.eo_bvsmulo
  | Eo.UserOp.bvusubo => schema.Constructor.eo_bvusubo
  | Eo.UserOp.bvssubo => schema.Constructor.eo_bvssubo
  | Eo.UserOp.bvsdivo => schema.Constructor.eo_bvsdivo
  | Eo.UserOp.bvultbv => schema.Constructor.eo_bvultbv
  | Eo.UserOp.bvsltbv => schema.Constructor.eo_bvsltbv
  | Eo.UserOp.bvredand => schema.Constructor.eo_bvredand
  | Eo.UserOp.bvredor => schema.Constructor.eo_bvredor
  | Eo.UserOp._at_from_bools => schema.Constructor.eo__40from_5fbools
  | Eo.UserOp.RegLan => schema.Constructor.eo_RegLan
  | Eo.UserOp.str_len => schema.Constructor.eo_str_2elen
  | Eo.UserOp.str_concat => schema.Constructor.eo_str_2e_2b_2b
  | Eo.UserOp.str_substr => schema.Constructor.eo_str_2esubstr
  | Eo.UserOp.str_contains => schema.Constructor.eo_str_2econtains
  | Eo.UserOp.str_replace => schema.Constructor.eo_str_2ereplace
  | Eo.UserOp.str_indexof => schema.Constructor.eo_str_2eindexof
  | Eo.UserOp.str_at => schema.Constructor.eo_str_2eat
  | Eo.UserOp.str_prefixof => schema.Constructor.eo_str_2eprefixof
  | Eo.UserOp.str_suffixof => schema.Constructor.eo_str_2esuffixof
  | Eo.UserOp.str_rev => schema.Constructor.eo_str_2erev
  | Eo.UserOp.str_update => schema.Constructor.eo_str_2eupdate
  | Eo.UserOp.str_to_lower => schema.Constructor.eo_str_2eto_5flower
  | Eo.UserOp.str_to_upper => schema.Constructor.eo_str_2eto_5fupper
  | Eo.UserOp.str_to_code => schema.Constructor.eo_str_2eto_5fcode
  | Eo.UserOp.str_from_code => schema.Constructor.eo_str_2efrom_5fcode
  | Eo.UserOp.str_is_digit => schema.Constructor.eo_str_2eis_5fdigit
  | Eo.UserOp.str_to_int => schema.Constructor.eo_str_2eto_5fint
  | Eo.UserOp.str_from_int => schema.Constructor.eo_str_2efrom_5fint
  | Eo.UserOp.str_lt => schema.Constructor.eo_str_2e_3c
  | Eo.UserOp.str_leq => schema.Constructor.eo_str_2e_3c_3d
  | Eo.UserOp.str_replace_all => schema.Constructor.eo_str_2ereplace_5fall
  | Eo.UserOp.str_replace_re => schema.Constructor.eo_str_2ereplace_5fre
  | Eo.UserOp.str_replace_re_all => schema.Constructor.eo_str_2ereplace_5fre_5fall
  | Eo.UserOp.str_indexof_re => schema.Constructor.eo_str_2eindexof_5fre
  | Eo.UserOp.re_allchar => schema.Constructor.eo_re_2eallchar
  | Eo.UserOp.re_none => schema.Constructor.eo_re_2enone
  | Eo.UserOp.re_all => schema.Constructor.eo_re_2eall
  | Eo.UserOp.str_to_re => schema.Constructor.eo_str_2eto_5fre
  | Eo.UserOp.re_mult => schema.Constructor.eo_re_2e_2a
  | Eo.UserOp.re_plus => schema.Constructor.eo_re_2e_2b
  | Eo.UserOp.re_opt => schema.Constructor.eo_re_2eopt
  | Eo.UserOp.re_comp => schema.Constructor.eo_re_2ecomp
  | Eo.UserOp.re_range => schema.Constructor.eo_re_2erange
  | Eo.UserOp.re_concat => schema.Constructor.eo_re_2e_2b_2b
  | Eo.UserOp.re_inter => schema.Constructor.eo_re_2einter
  | Eo.UserOp.re_union => schema.Constructor.eo_re_2eunion
  | Eo.UserOp.re_diff => schema.Constructor.eo_re_2ediff
  | Eo.UserOp.str_in_re => schema.Constructor.eo_str_2ein_5fre
  | Eo.UserOp.seq_unit => schema.Constructor.eo_seq_2eunit
  | Eo.UserOp.seq_nth => schema.Constructor.eo_seq_2enth
  | Eo.UserOp._at_strings_deq_diff => schema.Constructor.eo__40strings_5fdeq_5fdiff
  | Eo.UserOp._at_strings_stoi_result => schema.Constructor.eo__40strings_5fstoi_5fresult
  | Eo.UserOp._at_strings_stoi_non_digit => schema.Constructor.eo__40strings_5fstoi_5fnon_5fdigit
  | Eo.UserOp._at_strings_itos_result => schema.Constructor.eo__40strings_5fitos_5fresult
  | Eo.UserOp._at_strings_num_occur => schema.Constructor.eo__40strings_5fnum_5foccur
  | Eo.UserOp._at_strings_num_occur_re => schema.Constructor.eo__40strings_5fnum_5foccur_5fre
  | Eo.UserOp._at_strings_occur_index => schema.Constructor.eo__40strings_5foccur_5findex
  | Eo.UserOp._at_strings_occur_index_re => schema.Constructor.eo__40strings_5foccur_5findex_5fre
  | Eo.UserOp._at_strings_replace_all_result => schema.Constructor.eo__40strings_5freplace_5fall_5fresult
  | Eo.UserOp._at_strings_replace_re_all_result => schema.Constructor.eo__40strings_5freplace_5fre_5fall_5fresult
  | Eo.UserOp.UnitTuple => schema.Constructor.eo_UnitTuple
  | Eo.UserOp.Tuple => schema.Constructor.eo_Tuple
  | Eo.UserOp.tuple_unit => schema.Constructor.eo_tuple_2eunit
  | Eo.UserOp.tuple => schema.Constructor.eo_tuple
  | Eo.UserOp.Set => schema.Constructor.eo_Set
  | Eo.UserOp.set_singleton => schema.Constructor.eo_set_2esingleton
  | Eo.UserOp.set_union => schema.Constructor.eo_set_2eunion
  | Eo.UserOp.set_inter => schema.Constructor.eo_set_2einter
  | Eo.UserOp.set_minus => schema.Constructor.eo_set_2eminus
  | Eo.UserOp.set_member => schema.Constructor.eo_set_2emember
  | Eo.UserOp.set_subset => schema.Constructor.eo_set_2esubset
  | Eo.UserOp.set_choose => schema.Constructor.eo_set_2echoose
  | Eo.UserOp.set_is_empty => schema.Constructor.eo_set_2eis_5fempty
  | Eo.UserOp.set_is_singleton => schema.Constructor.eo_set_2eis_5fsingleton
  | Eo.UserOp.set_insert => schema.Constructor.eo_set_2einsert
  | Eo.UserOp._at_sets_deq_diff => schema.Constructor.eo__40sets_5fdeq_5fdiff
  | Eo.UserOp.qdiv => schema.Constructor.eo__2f
  | Eo.UserOp.qdiv_total => schema.Constructor.eo__2f_5ftotal
  | Eo.UserOp._at_div_by_zero => schema.Constructor.eo__40div_5fby_5fzero
  | Eo.UserOp._at__at_Monomial => schema.Constructor.eo__40_40Monomial
  | Eo.UserOp._at__at_mon => schema.Constructor.eo__40_40mon
  | Eo.UserOp._at__at_Polynomial => schema.Constructor.eo__40_40Polynomial
  | Eo.UserOp._at__at_poly_zero => schema.Constructor.eo__40_40poly_2ezero
  | Eo.UserOp._at__at_poly => schema.Constructor.eo__40_40poly
  | Eo.UserOp.forall => schema.Constructor.eo_forall
  | Eo.UserOp.exists => schema.Constructor.eo_exists
  | Eo.UserOp.ubv_to_int => schema.Constructor.eo_ubv_5fto_5fint
  | Eo.UserOp.sbv_to_int => schema.Constructor.eo_sbv_5fto_5fint
  | Eo.UserOp._at__at_aci_sorted => schema.Constructor.eo__40_40aci_5fsorted

/-- The constructor of the store for a user operator with 1 index. -/
def uop1 : Eo.UserOp1 → schema.Constructor
  | Eo.UserOp1.repeat => schema.Constructor.eo_repeat
  | Eo.UserOp1.zero_extend => schema.Constructor.eo_zero_5fextend
  | Eo.UserOp1.sign_extend => schema.Constructor.eo_sign_5fextend
  | Eo.UserOp1.rotate_left => schema.Constructor.eo_rotate_5fleft
  | Eo.UserOp1.rotate_right => schema.Constructor.eo_rotate_5fright
  | Eo.UserOp1._at_bit => schema.Constructor.eo__40bit
  | Eo.UserOp1.seq_empty => schema.Constructor.eo_seq_2eempty
  | Eo.UserOp1.re_exp => schema.Constructor.eo_re_2e_5e
  | Eo.UserOp1.is => schema.Constructor.eo_is
  | Eo.UserOp1.update => schema.Constructor.eo_update
  | Eo.UserOp1.tuple_select => schema.Constructor.eo_tuple_2eselect
  | Eo.UserOp1.tuple_update => schema.Constructor.eo_tuple_2eupdate
  | Eo.UserOp1.set_empty => schema.Constructor.eo_set_2eempty
  | Eo.UserOp1.int_to_bv => schema.Constructor.eo_int_5fto_5fbv

/-- The constructor of the store for a user operator with 2 indices. -/
def uop2 : Eo.UserOp2 → schema.Constructor
  | Eo.UserOp2.extract => schema.Constructor.eo_extract
  | Eo.UserOp2.re_loop => schema.Constructor.eo_re_2eloop
  | Eo.UserOp2._at_quantifiers_skolemize => schema.Constructor.eo__40quantifiers_5fskolemize
  | Eo.UserOp2._at_const => schema.Constructor.eo__40const

/-- The constructor of the store for a user operator with 3 indices. -/
def uop3 : Eo.UserOp3 → schema.Constructor
  | Eo.UserOp3._at_re_unfold_pos_component => schema.Constructor.eo__40re_5funfold_5fpos_5fcomponent
  | Eo.UserOp3._at_witness_string_length => schema.Constructor.eo__40witness_5fstring_5flength

@[simp] theorem mk_uop1_of_ne {op : Eo.UserOp1} {x1 : Eo.Term} (h1 : x1 ≠ Eo.Term.Stuck) :
    Eo.__eo_mk_uop1 op x1 = Eo.Term.UOp1 op x1 := by
  unfold Eo.__eo_mk_uop1; split <;> simp_all

@[simp] theorem mk_uop2_of_ne {op : Eo.UserOp2} {x1 x2 : Eo.Term} (h1 : x1 ≠ Eo.Term.Stuck) (h2 : x2 ≠ Eo.Term.Stuck) :
    Eo.__eo_mk_uop2 op x1 x2 = Eo.Term.UOp2 op x1 x2 := by
  unfold Eo.__eo_mk_uop2; split <;> simp_all

@[simp] theorem mk_uop3_of_ne {op : Eo.UserOp3} {x1 x2 x3 : Eo.Term} (h1 : x1 ≠ Eo.Term.Stuck) (h2 : x2 ≠ Eo.Term.Stuck) (h3 : x3 ≠ Eo.Term.Stuck) :
    Eo.__eo_mk_uop3 op x1 x2 x3 = Eo.Term.UOp3 op x1 x2 x3 := by
  unfold Eo.__eo_mk_uop3; split <;> simp_all

@[simp] theorem mk_var_of_ne {x1 x2 : Eo.Term} (h1 : x1 ≠ Eo.Term.Stuck) (h2 : x2 ≠ Eo.Term.Stuck) :
    Eo.__eo_mk_var x1 x2 = Eo.Term.Var x1 x2 := by
  unfold Eo.__eo_mk_var; split <;> simp_all

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
  | Eo.Term.UOp1 x0 x1 => Tree.node (uop1 x0) [(enc_Term x1)]
  | Eo.Term.UOp2 x0 x1 x2 => Tree.node (uop2 x0) [(enc_Term x1), (enc_Term x2)]
  | Eo.Term.UOp3 x0 x1 x2 x3 => Tree.node (uop3 x0) [(enc_Term x1), (enc_Term x2), (enc_Term x3)]
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
  | Tree.node schema.Constructor.eo__40_40Pair [] => some (Eo.Term.UOp Eo.UserOp._at__at_Pair)
  | Tree.node schema.Constructor.eo__40_40pair [] => some (Eo.Term.UOp Eo.UserOp._at__at_pair)
  | Tree.node schema.Constructor.eo__40_40TypedList [] => some (Eo.Term.UOp Eo.UserOp._at__at_TypedList)
  | Tree.node schema.Constructor.eo__40_40TypedList_2enil [] => some (Eo.Term.UOp Eo.UserOp._at__at_TypedList_nil)
  | Tree.node schema.Constructor.eo__40_40TypedList_2econs [] => some (Eo.Term.UOp Eo.UserOp._at__at_TypedList_cons)
  | Tree.node schema.Constructor.eo_ite [] => some (Eo.Term.UOp Eo.UserOp.ite)
  | Tree.node schema.Constructor.eo_not [] => some (Eo.Term.UOp Eo.UserOp.not)
  | Tree.node schema.Constructor.eo_or [] => some (Eo.Term.UOp Eo.UserOp.or)
  | Tree.node schema.Constructor.eo_and [] => some (Eo.Term.UOp Eo.UserOp.and)
  | Tree.node schema.Constructor.eo__3d_3e [] => some (Eo.Term.UOp Eo.UserOp.imp)
  | Tree.node schema.Constructor.eo_xor [] => some (Eo.Term.UOp Eo.UserOp.xor)
  | Tree.node schema.Constructor.eo__3d [] => some (Eo.Term.UOp Eo.UserOp.eq)
  | Tree.node schema.Constructor.eo_lambda [] => some (Eo.Term.UOp Eo.UserOp.lambda)
  | Tree.node schema.Constructor.eo_distinct [] => some (Eo.Term.UOp Eo.UserOp.distinct)
  | Tree.node schema.Constructor.eo__40purify [] => some (Eo.Term.UOp Eo.UserOp._at_purify)
  | Tree.node schema.Constructor.eo__2b [] => some (Eo.Term.UOp Eo.UserOp.plus)
  | Tree.node schema.Constructor.eo__2d [] => some (Eo.Term.UOp Eo.UserOp.neg)
  | Tree.node schema.Constructor.eo__2a [] => some (Eo.Term.UOp Eo.UserOp.mult)
  | Tree.node schema.Constructor.eo__3c [] => some (Eo.Term.UOp Eo.UserOp.lt)
  | Tree.node schema.Constructor.eo__3c_3d [] => some (Eo.Term.UOp Eo.UserOp.leq)
  | Tree.node schema.Constructor.eo__3e [] => some (Eo.Term.UOp Eo.UserOp.gt)
  | Tree.node schema.Constructor.eo__3e_3d [] => some (Eo.Term.UOp Eo.UserOp.geq)
  | Tree.node schema.Constructor.eo_to_5freal [] => some (Eo.Term.UOp Eo.UserOp.to_real)
  | Tree.node schema.Constructor.eo_to_5fint [] => some (Eo.Term.UOp Eo.UserOp.to_int)
  | Tree.node schema.Constructor.eo_is_5fint [] => some (Eo.Term.UOp Eo.UserOp.is_int)
  | Tree.node schema.Constructor.eo_abs [] => some (Eo.Term.UOp Eo.UserOp.abs)
  | Tree.node schema.Constructor.eo__24eoo_5f_2d_2e2 [] => some (Eo.Term.UOp Eo.UserOp.__eoo_neg_2)
  | Tree.node schema.Constructor.eo_div [] => some (Eo.Term.UOp Eo.UserOp.div)
  | Tree.node schema.Constructor.eo_mod [] => some (Eo.Term.UOp Eo.UserOp.mod)
  | Tree.node schema.Constructor.eo_divisible [] => some (Eo.Term.UOp Eo.UserOp.divisible)
  | Tree.node schema.Constructor.eo_int_2epow2 [] => some (Eo.Term.UOp Eo.UserOp.int_pow2)
  | Tree.node schema.Constructor.eo_int_2elog2 [] => some (Eo.Term.UOp Eo.UserOp.int_log2)
  | Tree.node schema.Constructor.eo_int_2eispow2 [] => some (Eo.Term.UOp Eo.UserOp.int_ispow2)
  | Tree.node schema.Constructor.eo_div_5ftotal [] => some (Eo.Term.UOp Eo.UserOp.div_total)
  | Tree.node schema.Constructor.eo_mod_5ftotal [] => some (Eo.Term.UOp Eo.UserOp.mod_total)
  | Tree.node schema.Constructor.eo__40int_5fdiv_5fby_5fzero [] => some (Eo.Term.UOp Eo.UserOp._at_int_div_by_zero)
  | Tree.node schema.Constructor.eo__40mod_5fby_5fzero [] => some (Eo.Term.UOp Eo.UserOp._at_mod_by_zero)
  | Tree.node schema.Constructor.eo_Array [] => some (Eo.Term.UOp Eo.UserOp.Array)
  | Tree.node schema.Constructor.eo_select [] => some (Eo.Term.UOp Eo.UserOp.select)
  | Tree.node schema.Constructor.eo_store [] => some (Eo.Term.UOp Eo.UserOp.store)
  | Tree.node schema.Constructor.eo__40array_5fdeq_5fdiff [] => some (Eo.Term.UOp Eo.UserOp._at_array_deq_diff)
  | Tree.node schema.Constructor.eo__40bvsize [] => some (Eo.Term.UOp Eo.UserOp._at_bvsize)
  | Tree.node schema.Constructor.eo_concat [] => some (Eo.Term.UOp Eo.UserOp.concat)
  | Tree.node schema.Constructor.eo_bvnot [] => some (Eo.Term.UOp Eo.UserOp.bvnot)
  | Tree.node schema.Constructor.eo_bvand [] => some (Eo.Term.UOp Eo.UserOp.bvand)
  | Tree.node schema.Constructor.eo_bvor [] => some (Eo.Term.UOp Eo.UserOp.bvor)
  | Tree.node schema.Constructor.eo_bvnand [] => some (Eo.Term.UOp Eo.UserOp.bvnand)
  | Tree.node schema.Constructor.eo_bvnor [] => some (Eo.Term.UOp Eo.UserOp.bvnor)
  | Tree.node schema.Constructor.eo_bvxor [] => some (Eo.Term.UOp Eo.UserOp.bvxor)
  | Tree.node schema.Constructor.eo_bvxnor [] => some (Eo.Term.UOp Eo.UserOp.bvxnor)
  | Tree.node schema.Constructor.eo_bvcomp [] => some (Eo.Term.UOp Eo.UserOp.bvcomp)
  | Tree.node schema.Constructor.eo_bvneg [] => some (Eo.Term.UOp Eo.UserOp.bvneg)
  | Tree.node schema.Constructor.eo_bvadd [] => some (Eo.Term.UOp Eo.UserOp.bvadd)
  | Tree.node schema.Constructor.eo_bvmul [] => some (Eo.Term.UOp Eo.UserOp.bvmul)
  | Tree.node schema.Constructor.eo_bvudiv [] => some (Eo.Term.UOp Eo.UserOp.bvudiv)
  | Tree.node schema.Constructor.eo_bvurem [] => some (Eo.Term.UOp Eo.UserOp.bvurem)
  | Tree.node schema.Constructor.eo_bvsub [] => some (Eo.Term.UOp Eo.UserOp.bvsub)
  | Tree.node schema.Constructor.eo_bvsdiv [] => some (Eo.Term.UOp Eo.UserOp.bvsdiv)
  | Tree.node schema.Constructor.eo_bvsrem [] => some (Eo.Term.UOp Eo.UserOp.bvsrem)
  | Tree.node schema.Constructor.eo_bvsmod [] => some (Eo.Term.UOp Eo.UserOp.bvsmod)
  | Tree.node schema.Constructor.eo_bvult [] => some (Eo.Term.UOp Eo.UserOp.bvult)
  | Tree.node schema.Constructor.eo_bvule [] => some (Eo.Term.UOp Eo.UserOp.bvule)
  | Tree.node schema.Constructor.eo_bvugt [] => some (Eo.Term.UOp Eo.UserOp.bvugt)
  | Tree.node schema.Constructor.eo_bvuge [] => some (Eo.Term.UOp Eo.UserOp.bvuge)
  | Tree.node schema.Constructor.eo_bvslt [] => some (Eo.Term.UOp Eo.UserOp.bvslt)
  | Tree.node schema.Constructor.eo_bvsle [] => some (Eo.Term.UOp Eo.UserOp.bvsle)
  | Tree.node schema.Constructor.eo_bvsgt [] => some (Eo.Term.UOp Eo.UserOp.bvsgt)
  | Tree.node schema.Constructor.eo_bvsge [] => some (Eo.Term.UOp Eo.UserOp.bvsge)
  | Tree.node schema.Constructor.eo_bvshl [] => some (Eo.Term.UOp Eo.UserOp.bvshl)
  | Tree.node schema.Constructor.eo_bvlshr [] => some (Eo.Term.UOp Eo.UserOp.bvlshr)
  | Tree.node schema.Constructor.eo_bvashr [] => some (Eo.Term.UOp Eo.UserOp.bvashr)
  | Tree.node schema.Constructor.eo_bvite [] => some (Eo.Term.UOp Eo.UserOp.bvite)
  | Tree.node schema.Constructor.eo_bvuaddo [] => some (Eo.Term.UOp Eo.UserOp.bvuaddo)
  | Tree.node schema.Constructor.eo_bvnego [] => some (Eo.Term.UOp Eo.UserOp.bvnego)
  | Tree.node schema.Constructor.eo_bvsaddo [] => some (Eo.Term.UOp Eo.UserOp.bvsaddo)
  | Tree.node schema.Constructor.eo_bvumulo [] => some (Eo.Term.UOp Eo.UserOp.bvumulo)
  | Tree.node schema.Constructor.eo_bvsmulo [] => some (Eo.Term.UOp Eo.UserOp.bvsmulo)
  | Tree.node schema.Constructor.eo_bvusubo [] => some (Eo.Term.UOp Eo.UserOp.bvusubo)
  | Tree.node schema.Constructor.eo_bvssubo [] => some (Eo.Term.UOp Eo.UserOp.bvssubo)
  | Tree.node schema.Constructor.eo_bvsdivo [] => some (Eo.Term.UOp Eo.UserOp.bvsdivo)
  | Tree.node schema.Constructor.eo_bvultbv [] => some (Eo.Term.UOp Eo.UserOp.bvultbv)
  | Tree.node schema.Constructor.eo_bvsltbv [] => some (Eo.Term.UOp Eo.UserOp.bvsltbv)
  | Tree.node schema.Constructor.eo_bvredand [] => some (Eo.Term.UOp Eo.UserOp.bvredand)
  | Tree.node schema.Constructor.eo_bvredor [] => some (Eo.Term.UOp Eo.UserOp.bvredor)
  | Tree.node schema.Constructor.eo__40from_5fbools [] => some (Eo.Term.UOp Eo.UserOp._at_from_bools)
  | Tree.node schema.Constructor.eo_RegLan [] => some (Eo.Term.UOp Eo.UserOp.RegLan)
  | Tree.node schema.Constructor.eo_str_2elen [] => some (Eo.Term.UOp Eo.UserOp.str_len)
  | Tree.node schema.Constructor.eo_str_2e_2b_2b [] => some (Eo.Term.UOp Eo.UserOp.str_concat)
  | Tree.node schema.Constructor.eo_str_2esubstr [] => some (Eo.Term.UOp Eo.UserOp.str_substr)
  | Tree.node schema.Constructor.eo_str_2econtains [] => some (Eo.Term.UOp Eo.UserOp.str_contains)
  | Tree.node schema.Constructor.eo_str_2ereplace [] => some (Eo.Term.UOp Eo.UserOp.str_replace)
  | Tree.node schema.Constructor.eo_str_2eindexof [] => some (Eo.Term.UOp Eo.UserOp.str_indexof)
  | Tree.node schema.Constructor.eo_str_2eat [] => some (Eo.Term.UOp Eo.UserOp.str_at)
  | Tree.node schema.Constructor.eo_str_2eprefixof [] => some (Eo.Term.UOp Eo.UserOp.str_prefixof)
  | Tree.node schema.Constructor.eo_str_2esuffixof [] => some (Eo.Term.UOp Eo.UserOp.str_suffixof)
  | Tree.node schema.Constructor.eo_str_2erev [] => some (Eo.Term.UOp Eo.UserOp.str_rev)
  | Tree.node schema.Constructor.eo_str_2eupdate [] => some (Eo.Term.UOp Eo.UserOp.str_update)
  | Tree.node schema.Constructor.eo_str_2eto_5flower [] => some (Eo.Term.UOp Eo.UserOp.str_to_lower)
  | Tree.node schema.Constructor.eo_str_2eto_5fupper [] => some (Eo.Term.UOp Eo.UserOp.str_to_upper)
  | Tree.node schema.Constructor.eo_str_2eto_5fcode [] => some (Eo.Term.UOp Eo.UserOp.str_to_code)
  | Tree.node schema.Constructor.eo_str_2efrom_5fcode [] => some (Eo.Term.UOp Eo.UserOp.str_from_code)
  | Tree.node schema.Constructor.eo_str_2eis_5fdigit [] => some (Eo.Term.UOp Eo.UserOp.str_is_digit)
  | Tree.node schema.Constructor.eo_str_2eto_5fint [] => some (Eo.Term.UOp Eo.UserOp.str_to_int)
  | Tree.node schema.Constructor.eo_str_2efrom_5fint [] => some (Eo.Term.UOp Eo.UserOp.str_from_int)
  | Tree.node schema.Constructor.eo_str_2e_3c [] => some (Eo.Term.UOp Eo.UserOp.str_lt)
  | Tree.node schema.Constructor.eo_str_2e_3c_3d [] => some (Eo.Term.UOp Eo.UserOp.str_leq)
  | Tree.node schema.Constructor.eo_str_2ereplace_5fall [] => some (Eo.Term.UOp Eo.UserOp.str_replace_all)
  | Tree.node schema.Constructor.eo_str_2ereplace_5fre [] => some (Eo.Term.UOp Eo.UserOp.str_replace_re)
  | Tree.node schema.Constructor.eo_str_2ereplace_5fre_5fall [] => some (Eo.Term.UOp Eo.UserOp.str_replace_re_all)
  | Tree.node schema.Constructor.eo_str_2eindexof_5fre [] => some (Eo.Term.UOp Eo.UserOp.str_indexof_re)
  | Tree.node schema.Constructor.eo_re_2eallchar [] => some (Eo.Term.UOp Eo.UserOp.re_allchar)
  | Tree.node schema.Constructor.eo_re_2enone [] => some (Eo.Term.UOp Eo.UserOp.re_none)
  | Tree.node schema.Constructor.eo_re_2eall [] => some (Eo.Term.UOp Eo.UserOp.re_all)
  | Tree.node schema.Constructor.eo_str_2eto_5fre [] => some (Eo.Term.UOp Eo.UserOp.str_to_re)
  | Tree.node schema.Constructor.eo_re_2e_2a [] => some (Eo.Term.UOp Eo.UserOp.re_mult)
  | Tree.node schema.Constructor.eo_re_2e_2b [] => some (Eo.Term.UOp Eo.UserOp.re_plus)
  | Tree.node schema.Constructor.eo_re_2eopt [] => some (Eo.Term.UOp Eo.UserOp.re_opt)
  | Tree.node schema.Constructor.eo_re_2ecomp [] => some (Eo.Term.UOp Eo.UserOp.re_comp)
  | Tree.node schema.Constructor.eo_re_2erange [] => some (Eo.Term.UOp Eo.UserOp.re_range)
  | Tree.node schema.Constructor.eo_re_2e_2b_2b [] => some (Eo.Term.UOp Eo.UserOp.re_concat)
  | Tree.node schema.Constructor.eo_re_2einter [] => some (Eo.Term.UOp Eo.UserOp.re_inter)
  | Tree.node schema.Constructor.eo_re_2eunion [] => some (Eo.Term.UOp Eo.UserOp.re_union)
  | Tree.node schema.Constructor.eo_re_2ediff [] => some (Eo.Term.UOp Eo.UserOp.re_diff)
  | Tree.node schema.Constructor.eo_str_2ein_5fre [] => some (Eo.Term.UOp Eo.UserOp.str_in_re)
  | Tree.node schema.Constructor.eo_seq_2eunit [] => some (Eo.Term.UOp Eo.UserOp.seq_unit)
  | Tree.node schema.Constructor.eo_seq_2enth [] => some (Eo.Term.UOp Eo.UserOp.seq_nth)
  | Tree.node schema.Constructor.eo__40strings_5fdeq_5fdiff [] => some (Eo.Term.UOp Eo.UserOp._at_strings_deq_diff)
  | Tree.node schema.Constructor.eo__40strings_5fstoi_5fresult [] => some (Eo.Term.UOp Eo.UserOp._at_strings_stoi_result)
  | Tree.node schema.Constructor.eo__40strings_5fstoi_5fnon_5fdigit [] => some (Eo.Term.UOp Eo.UserOp._at_strings_stoi_non_digit)
  | Tree.node schema.Constructor.eo__40strings_5fitos_5fresult [] => some (Eo.Term.UOp Eo.UserOp._at_strings_itos_result)
  | Tree.node schema.Constructor.eo__40strings_5fnum_5foccur [] => some (Eo.Term.UOp Eo.UserOp._at_strings_num_occur)
  | Tree.node schema.Constructor.eo__40strings_5fnum_5foccur_5fre [] => some (Eo.Term.UOp Eo.UserOp._at_strings_num_occur_re)
  | Tree.node schema.Constructor.eo__40strings_5foccur_5findex [] => some (Eo.Term.UOp Eo.UserOp._at_strings_occur_index)
  | Tree.node schema.Constructor.eo__40strings_5foccur_5findex_5fre [] => some (Eo.Term.UOp Eo.UserOp._at_strings_occur_index_re)
  | Tree.node schema.Constructor.eo__40strings_5freplace_5fall_5fresult [] => some (Eo.Term.UOp Eo.UserOp._at_strings_replace_all_result)
  | Tree.node schema.Constructor.eo__40strings_5freplace_5fre_5fall_5fresult [] => some (Eo.Term.UOp Eo.UserOp._at_strings_replace_re_all_result)
  | Tree.node schema.Constructor.eo_UnitTuple [] => some (Eo.Term.UOp Eo.UserOp.UnitTuple)
  | Tree.node schema.Constructor.eo_Tuple [] => some (Eo.Term.UOp Eo.UserOp.Tuple)
  | Tree.node schema.Constructor.eo_tuple_2eunit [] => some (Eo.Term.UOp Eo.UserOp.tuple_unit)
  | Tree.node schema.Constructor.eo_tuple [] => some (Eo.Term.UOp Eo.UserOp.tuple)
  | Tree.node schema.Constructor.eo_Set [] => some (Eo.Term.UOp Eo.UserOp.Set)
  | Tree.node schema.Constructor.eo_set_2esingleton [] => some (Eo.Term.UOp Eo.UserOp.set_singleton)
  | Tree.node schema.Constructor.eo_set_2eunion [] => some (Eo.Term.UOp Eo.UserOp.set_union)
  | Tree.node schema.Constructor.eo_set_2einter [] => some (Eo.Term.UOp Eo.UserOp.set_inter)
  | Tree.node schema.Constructor.eo_set_2eminus [] => some (Eo.Term.UOp Eo.UserOp.set_minus)
  | Tree.node schema.Constructor.eo_set_2emember [] => some (Eo.Term.UOp Eo.UserOp.set_member)
  | Tree.node schema.Constructor.eo_set_2esubset [] => some (Eo.Term.UOp Eo.UserOp.set_subset)
  | Tree.node schema.Constructor.eo_set_2echoose [] => some (Eo.Term.UOp Eo.UserOp.set_choose)
  | Tree.node schema.Constructor.eo_set_2eis_5fempty [] => some (Eo.Term.UOp Eo.UserOp.set_is_empty)
  | Tree.node schema.Constructor.eo_set_2eis_5fsingleton [] => some (Eo.Term.UOp Eo.UserOp.set_is_singleton)
  | Tree.node schema.Constructor.eo_set_2einsert [] => some (Eo.Term.UOp Eo.UserOp.set_insert)
  | Tree.node schema.Constructor.eo__40sets_5fdeq_5fdiff [] => some (Eo.Term.UOp Eo.UserOp._at_sets_deq_diff)
  | Tree.node schema.Constructor.eo__2f [] => some (Eo.Term.UOp Eo.UserOp.qdiv)
  | Tree.node schema.Constructor.eo__2f_5ftotal [] => some (Eo.Term.UOp Eo.UserOp.qdiv_total)
  | Tree.node schema.Constructor.eo__40div_5fby_5fzero [] => some (Eo.Term.UOp Eo.UserOp._at_div_by_zero)
  | Tree.node schema.Constructor.eo__40_40Monomial [] => some (Eo.Term.UOp Eo.UserOp._at__at_Monomial)
  | Tree.node schema.Constructor.eo__40_40mon [] => some (Eo.Term.UOp Eo.UserOp._at__at_mon)
  | Tree.node schema.Constructor.eo__40_40Polynomial [] => some (Eo.Term.UOp Eo.UserOp._at__at_Polynomial)
  | Tree.node schema.Constructor.eo__40_40poly_2ezero [] => some (Eo.Term.UOp Eo.UserOp._at__at_poly_zero)
  | Tree.node schema.Constructor.eo__40_40poly [] => some (Eo.Term.UOp Eo.UserOp._at__at_poly)
  | Tree.node schema.Constructor.eo_forall [] => some (Eo.Term.UOp Eo.UserOp.forall)
  | Tree.node schema.Constructor.eo_exists [] => some (Eo.Term.UOp Eo.UserOp.exists)
  | Tree.node schema.Constructor.eo_ubv_5fto_5fint [] => some (Eo.Term.UOp Eo.UserOp.ubv_to_int)
  | Tree.node schema.Constructor.eo_sbv_5fto_5fint [] => some (Eo.Term.UOp Eo.UserOp.sbv_to_int)
  | Tree.node schema.Constructor.eo__40_40aci_5fsorted [] => some (Eo.Term.UOp Eo.UserOp._at__at_aci_sorted)
  | Tree.node schema.Constructor.eo_repeat [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.repeat x1)
  | Tree.node schema.Constructor.eo_zero_5fextend [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.zero_extend x1)
  | Tree.node schema.Constructor.eo_sign_5fextend [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.sign_extend x1)
  | Tree.node schema.Constructor.eo_rotate_5fleft [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.rotate_left x1)
  | Tree.node schema.Constructor.eo_rotate_5fright [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.rotate_right x1)
  | Tree.node schema.Constructor.eo__40bit [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1._at_bit x1)
  | Tree.node schema.Constructor.eo_seq_2eempty [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.seq_empty x1)
  | Tree.node schema.Constructor.eo_re_2e_5e [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.re_exp x1)
  | Tree.node schema.Constructor.eo_is [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.is x1)
  | Tree.node schema.Constructor.eo_update [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.update x1)
  | Tree.node schema.Constructor.eo_tuple_2eselect [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.tuple_select x1)
  | Tree.node schema.Constructor.eo_tuple_2eupdate [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.tuple_update x1)
  | Tree.node schema.Constructor.eo_set_2eempty [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.set_empty x1)
  | Tree.node schema.Constructor.eo_int_5fto_5fbv [t1] => do
    let x1 ← dec_Term t1
    some (Eo.Term.UOp1 Eo.UserOp1.int_to_bv x1)
  | Tree.node schema.Constructor.eo_extract [t1, t2] => do
    let x1 ← dec_Term t1
    let x2 ← dec_Term t2
    some (Eo.Term.UOp2 Eo.UserOp2.extract x1 x2)
  | Tree.node schema.Constructor.eo_re_2eloop [t1, t2] => do
    let x1 ← dec_Term t1
    let x2 ← dec_Term t2
    some (Eo.Term.UOp2 Eo.UserOp2.re_loop x1 x2)
  | Tree.node schema.Constructor.eo__40quantifiers_5fskolemize [t1, t2] => do
    let x1 ← dec_Term t1
    let x2 ← dec_Term t2
    some (Eo.Term.UOp2 Eo.UserOp2._at_quantifiers_skolemize x1 x2)
  | Tree.node schema.Constructor.eo__40const [t1, t2] => do
    let x1 ← dec_Term t1
    let x2 ← dec_Term t2
    some (Eo.Term.UOp2 Eo.UserOp2._at_const x1 x2)
  | Tree.node schema.Constructor.eo__40re_5funfold_5fpos_5fcomponent [t1, t2, t3] => do
    let x1 ← dec_Term t1
    let x2 ← dec_Term t2
    let x3 ← dec_Term t3
    some (Eo.Term.UOp3 Eo.UserOp3._at_re_unfold_pos_component x1 x2 x3)
  | Tree.node schema.Constructor.eo__40witness_5fstring_5flength [t1, t2, t3] => do
    let x1 ← dec_Term t1
    let x2 ← dec_Term t2
    let x3 ← dec_Term t3
    some (Eo.Term.UOp3 Eo.UserOp3._at_witness_string_length x1 x2 x3)
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
  | Eo.Term.UOp1 x0 x1 => emb_Term x1
  | Eo.Term.UOp2 x0 x1 x2 => emb_Term x1 ∧ emb_Term x2
  | Eo.Term.UOp3 x0 x1 x2 x3 => emb_Term x1 ∧ emb_Term x2 ∧ emb_Term x3
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
  | Eo.Term.UOp1 x0 x1, h => by
    simp only [emb_Term] at h
    have h1 := h
    cases x0 <;> (simp only [enc_Term, uop1]; unfold dec_Term; simp only [Option.bind_eq_bind, dec_enc_Term x1 h1, Option.bind_some])
  | Eo.Term.UOp2 x0 x1 x2, h => by
    simp only [emb_Term] at h
    obtain ⟨h1, h2⟩ := h
    cases x0 <;> (simp only [enc_Term, uop2]; unfold dec_Term; simp only [Option.bind_eq_bind, dec_enc_Term x1 h1, dec_enc_Term x2 h2, Option.bind_some])
  | Eo.Term.UOp3 x0 x1 x2 x3, h => by
    simp only [emb_Term] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases x0 <;> (simp only [enc_Term, uop3]; unfold dec_Term; simp only [Option.bind_eq_bind, dec_enc_Term x1 h1, dec_enc_Term x2 h2, dec_enc_Term x3 h3, Option.bind_some])
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

theorem inv_Term_UOp1_repeat {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_repeat ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.repeat x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_zero_extend {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_zero_5fextend ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.zero_extend x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_sign_extend {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_sign_5fextend ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.sign_extend x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_rotate_left {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_rotate_5fleft ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.rotate_left x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_rotate_right {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_rotate_5fright ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.rotate_right x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1__at_bit {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__40bit ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1._at_bit x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_seq_empty {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_seq_2eempty ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.seq_empty x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_re_exp {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_re_2e_5e ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.re_exp x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_is {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_is ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.is x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_update {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_update ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.update x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_tuple_select {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_tuple_2eselect ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.tuple_select x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_tuple_update {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_tuple_2eupdate ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.tuple_update x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_set_empty {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_set_2eempty ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.set_empty x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp1_int_to_bv {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_int_5fto_5fbv ts) (he : emb_Term x) :
    ∃ x0, x = Eo.Term.UOp1 Eo.UserOp1.int_to_bv x0 ∧ ts = [(enc_Term x0)] := by
  have hd := dec_enc_Term x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨_, _⟩⟩
  · unfold dec_Term at hd
    cases hd
  · unfold dec_Term at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, rfl⟩ := hd
    simp only [enc_Term, uop1, Tree.node.injEq, true_and] at h
    exact ⟨_, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp2_extract {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_extract ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.UOp2 Eo.UserOp2.extract x0 x1 ∧ ts = [(enc_Term x0), (enc_Term x1)] := by
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
    simp only [enc_Term, uop2, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp2_re_loop {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo_re_2eloop ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.UOp2 Eo.UserOp2.re_loop x0 x1 ∧ ts = [(enc_Term x0), (enc_Term x1)] := by
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
    simp only [enc_Term, uop2, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp2__at_quantifiers_skolemize {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__40quantifiers_5fskolemize ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.UOp2 Eo.UserOp2._at_quantifiers_skolemize x0 x1 ∧ ts = [(enc_Term x0), (enc_Term x1)] := by
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
    simp only [enc_Term, uop2, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp2__at_const {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__40const ts) (he : emb_Term x) :
    ∃ x0 x1, x = Eo.Term.UOp2 Eo.UserOp2._at_const x0 x1 ∧ ts = [(enc_Term x0), (enc_Term x1)] := by
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
    simp only [enc_Term, uop2, Tree.node.injEq, true_and] at h
    exact ⟨_, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp3__at_re_unfold_pos_component {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__40re_5funfold_5fpos_5fcomponent ts) (he : emb_Term x) :
    ∃ x0 x1 x2, x = Eo.Term.UOp3 Eo.UserOp3._at_re_unfold_pos_component x0 x1 x2 ∧ ts = [(enc_Term x0), (enc_Term x1), (enc_Term x2)] := by
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
    simp only [enc_Term, uop3, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_Term at hd
    cases hd

theorem inv_Term_UOp3__at_witness_string_length {x : Eo.Term} {ts : List Tree}
    (h : enc_Term x = Tree.node schema.Constructor.eo__40witness_5fstring_5flength ts) (he : emb_Term x) :
    ∃ x0 x1 x2, x = Eo.Term.UOp3 Eo.UserOp3._at_witness_string_length x0 x1 x2 ∧ ts = [(enc_Term x0), (enc_Term x1), (enc_Term x2)] := by
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
    simp only [enc_Term, uop3, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, rfl, h.symm⟩
  · unfold dec_Term at hd
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
  case «UOp1» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rename_i op _
    cases op <;> exact Or.inl rfl
  case «UOp2» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rename_i op _ _
    cases op <;> exact Or.inl rfl
  case «UOp3» =>
    simp only [enc_Term, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rename_i op _ _ _
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
  | Eo.CRule.process_scope => Tree.node schema.Constructor.eo__24emb_5fr_2eprocess_5fscope []
  | Eo.CRule.ite_eq => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq []
  | Eo.CRule.split => Tree.node schema.Constructor.eo__24emb_5fr_2esplit []
  | Eo.CRule.resolution => Tree.node schema.Constructor.eo__24emb_5fr_2eresolution []
  | Eo.CRule.chain_resolution => Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fresolution []
  | Eo.CRule.chain_m_resolution => Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution []
  | Eo.CRule.factoring => Tree.node schema.Constructor.eo__24emb_5fr_2efactoring []
  | Eo.CRule.reordering => Tree.node schema.Constructor.eo__24emb_5fr_2ereordering []
  | Eo.CRule.eq_resolve => Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fresolve []
  | Eo.CRule.modus_ponens => Tree.node schema.Constructor.eo__24emb_5fr_2emodus_5fponens []
  | Eo.CRule.not_not_elim => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim []
  | Eo.CRule.contra => Tree.node schema.Constructor.eo__24emb_5fr_2econtra []
  | Eo.CRule.and_elim => Tree.node schema.Constructor.eo__24emb_5fr_2eand_5felim []
  | Eo.CRule.and_intro => Tree.node schema.Constructor.eo__24emb_5fr_2eand_5fintro []
  | Eo.CRule.not_or_elim => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5for_5felim []
  | Eo.CRule.implies_elim => Tree.node schema.Constructor.eo__24emb_5fr_2eimplies_5felim []
  | Eo.CRule.not_implies_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 []
  | Eo.CRule.not_implies_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 []
  | Eo.CRule.equiv_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 []
  | Eo.CRule.equiv_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 []
  | Eo.CRule.not_equiv_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 []
  | Eo.CRule.not_equiv_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 []
  | Eo.CRule.xor_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim1 []
  | Eo.CRule.xor_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim2 []
  | Eo.CRule.not_xor_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 []
  | Eo.CRule.not_xor_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 []
  | Eo.CRule.ite_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim1 []
  | Eo.CRule.ite_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim2 []
  | Eo.CRule.not_ite_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 []
  | Eo.CRule.not_ite_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 []
  | Eo.CRule.not_and => Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fand []
  | Eo.CRule.cnf_and_pos => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos []
  | Eo.CRule.cnf_and_neg => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg []
  | Eo.CRule.cnf_or_pos => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos []
  | Eo.CRule.cnf_or_neg => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg []
  | Eo.CRule.cnf_implies_pos => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos []
  | Eo.CRule.cnf_implies_neg1 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 []
  | Eo.CRule.cnf_implies_neg2 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 []
  | Eo.CRule.cnf_equiv_pos1 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 []
  | Eo.CRule.cnf_equiv_pos2 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 []
  | Eo.CRule.cnf_equiv_neg1 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 []
  | Eo.CRule.cnf_equiv_neg2 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 []
  | Eo.CRule.cnf_xor_pos1 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 []
  | Eo.CRule.cnf_xor_pos2 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 []
  | Eo.CRule.cnf_xor_neg1 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 []
  | Eo.CRule.cnf_xor_neg2 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 []
  | Eo.CRule.cnf_ite_pos1 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 []
  | Eo.CRule.cnf_ite_pos2 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 []
  | Eo.CRule.cnf_ite_pos3 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 []
  | Eo.CRule.cnf_ite_neg1 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 []
  | Eo.CRule.cnf_ite_neg2 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 []
  | Eo.CRule.cnf_ite_neg3 => Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 []
  | Eo.CRule.arrays_read_over_write => Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite []
  | Eo.CRule.arrays_read_over_write_contra => Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra []
  | Eo.CRule.arrays_read_over_write_1 => Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 []
  | Eo.CRule.arrays_ext => Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fext []
  | Eo.CRule.refl => Tree.node schema.Constructor.eo__24emb_5fr_2erefl []
  | Eo.CRule.symm => Tree.node schema.Constructor.eo__24emb_5fr_2esymm []
  | Eo.CRule.trans => Tree.node schema.Constructor.eo__24emb_5fr_2etrans []
  | Eo.CRule.cong => Tree.node schema.Constructor.eo__24emb_5fr_2econg []
  | Eo.CRule.nary_cong => Tree.node schema.Constructor.eo__24emb_5fr_2enary_5fcong []
  | Eo.CRule.pairwise_cong => Tree.node schema.Constructor.eo__24emb_5fr_2epairwise_5fcong []
  | Eo.CRule.true_intro => Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5fintro []
  | Eo.CRule.true_elim => Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5felim []
  | Eo.CRule.false_intro => Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5fintro []
  | Eo.CRule.false_elim => Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5felim []
  | Eo.CRule.ho_cong => Tree.node schema.Constructor.eo__24emb_5fr_2eho_5fcong []
  | Eo.CRule.distinct_elim => Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5felim []
  | Eo.CRule.distinct_true => Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue []
  | Eo.CRule.distinct_false => Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse []
  | Eo.CRule.arith_sum_ub => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub []
  | Eo.CRule.arith_mult_pos => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos []
  | Eo.CRule.arith_mult_neg => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg []
  | Eo.CRule.arith_trichotomy => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy []
  | Eo.CRule.int_tight_ub => Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub []
  | Eo.CRule.int_tight_lb => Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb []
  | Eo.CRule.arith_mult_tangent => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent []
  | Eo.CRule.arith_mult_sign => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign []
  | Eo.CRule.arith_mult_abs_comparison => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison []
  | Eo.CRule.arith_reduction => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5freduction []
  | Eo.CRule.arith_poly_norm => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm []
  | Eo.CRule.arith_poly_norm_rel => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel []
  | Eo.CRule.bv_repeat_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim []
  | Eo.CRule.bv_smulo_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim []
  | Eo.CRule.bv_umulo_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim []
  | Eo.CRule.bv_bitwise_slicing => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing []
  | Eo.CRule.bv_bitblast_step => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep []
  | Eo.CRule.bv_poly_norm => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm []
  | Eo.CRule.bv_poly_norm_eq => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq []
  | Eo.CRule.string_length_pos => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos []
  | Eo.CRule.string_length_non_empty => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty []
  | Eo.CRule.concat_eq => Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5feq []
  | Eo.CRule.concat_unify => Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5funify []
  | Eo.CRule.concat_csplit => Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit []
  | Eo.CRule.concat_split => Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fsplit []
  | Eo.CRule.concat_lprop => Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5flprop []
  | Eo.CRule.concat_cprop => Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcprop []
  | Eo.CRule.string_decompose => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fdecompose []
  | Eo.CRule.exists_string_length => Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength []
  | Eo.CRule.string_code_inj => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj []
  | Eo.CRule.string_seq_unit_inj => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj []
  | Eo.CRule.re_inter => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter []
  | Eo.CRule.re_concat => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat []
  | Eo.CRule.re_unfold_pos => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos []
  | Eo.CRule.re_unfold_neg_concat_fixed => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed []
  | Eo.CRule.re_unfold_neg => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg []
  | Eo.CRule.string_ext => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fext []
  | Eo.CRule.string_reduction => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5freduction []
  | Eo.CRule.string_eager_reduction => Tree.node schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction []
  | Eo.CRule.arith_string_pred_entail => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail []
  | Eo.CRule.arith_string_pred_safe_approx => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox []
  | Eo.CRule.str_in_re_eval => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval []
  | Eo.CRule.str_in_re_consume => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume []
  | Eo.CRule.re_loop_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim []
  | Eo.CRule.re_eq_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim []
  | Eo.CRule.re_inter_inclusion => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion []
  | Eo.CRule.re_union_inclusion => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion []
  | Eo.CRule.str_in_re_concat_star_char => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar []
  | Eo.CRule.str_in_re_sigma => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma []
  | Eo.CRule.str_in_re_sigma_star => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar []
  | Eo.CRule.str_ctn_multiset_subset => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset []
  | Eo.CRule.str_overlap_split_ctn => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn []
  | Eo.CRule.str_overlap_endpoints_ctn => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn []
  | Eo.CRule.str_overlap_endpoints_indexof => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof []
  | Eo.CRule.str_overlap_endpoints_replace => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace []
  | Eo.CRule.str_indexof_re_eval => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval []
  | Eo.CRule.str_replace_re_eval => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval []
  | Eo.CRule.str_replace_re_all_eval => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval []
  | Eo.CRule.seq_eval_op => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop []
  | Eo.CRule.sets_singleton_inj => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj []
  | Eo.CRule.sets_ext => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fext []
  | Eo.CRule.sets_choose_member => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember []
  | Eo.CRule.sets_eval_op => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop []
  | Eo.CRule.ubv_to_int_range => Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange []
  | Eo.CRule.ubv_to_int_elim => Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim []
  | Eo.CRule.int_to_bv_elim => Tree.node schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim []
  | Eo.CRule.instantiate => Tree.node schema.Constructor.eo__24emb_5fr_2einstantiate []
  | Eo.CRule.skolemize => Tree.node schema.Constructor.eo__24emb_5fr_2eskolemize []
  | Eo.CRule.skolem_intro => Tree.node schema.Constructor.eo__24emb_5fr_2eskolem_5fintro []
  | Eo.CRule.alpha_equiv => Tree.node schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv []
  | Eo.CRule.beta_reduce => Tree.node schema.Constructor.eo__24emb_5fr_2ebeta_5freduce []
  | Eo.CRule.quant_var_reordering => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering []
  | Eo.CRule.exists_elim => Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5felim []
  | Eo.CRule.quant_unused_vars => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars []
  | Eo.CRule.quant_merge_prenex => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex []
  | Eo.CRule.quant_miniscope_and => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand []
  | Eo.CRule.quant_miniscope_or => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for []
  | Eo.CRule.quant_miniscope_ite => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite []
  | Eo.CRule.quant_var_elim_eq => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq []
  | Eo.CRule.quant_dt_split => Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit []
  | Eo.CRule.dt_split => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fsplit []
  | Eo.CRule.dt_inst => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5finst []
  | Eo.CRule.dt_collapse_selector => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector []
  | Eo.CRule.dt_collapse_tester => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester []
  | Eo.CRule.dt_collapse_tester_singleton => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton []
  | Eo.CRule.dt_cons_eq => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq []
  | Eo.CRule.dt_cons_eq_clash => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash []
  | Eo.CRule.dt_cycle => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcycle []
  | Eo.CRule.dt_collapse_updater => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater []
  | Eo.CRule.dt_updater_elim => Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim []
  | Eo.CRule.arith_div_total_zero_real => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal []
  | Eo.CRule.arith_div_total_zero_int => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint []
  | Eo.CRule.arith_int_div_total => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal []
  | Eo.CRule.arith_int_div_total_one => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone []
  | Eo.CRule.arith_int_div_total_zero => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero []
  | Eo.CRule.arith_int_div_total_neg => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg []
  | Eo.CRule.arith_int_mod_total => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal []
  | Eo.CRule.arith_int_mod_total_one => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone []
  | Eo.CRule.arith_int_mod_total_zero => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero []
  | Eo.CRule.arith_int_mod_total_neg => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg []
  | Eo.CRule.arith_int_div_total_over_mod => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod []
  | Eo.CRule.arith_elim_gt => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt []
  | Eo.CRule.arith_elim_lt => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt []
  | Eo.CRule.arith_elim_int_gt => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt []
  | Eo.CRule.arith_elim_int_lt => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt []
  | Eo.CRule.arith_elim_leq => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq []
  | Eo.CRule.arith_leq_norm => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm []
  | Eo.CRule.arith_geq_tighten => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten []
  | Eo.CRule.arith_geq_norm1_int => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint []
  | Eo.CRule.arith_geq_norm1_real => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal []
  | Eo.CRule.arith_eq_elim_real => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal []
  | Eo.CRule.arith_eq_elim_int => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint []
  | Eo.CRule.arith_to_int_elim_to_real => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal []
  | Eo.CRule.arith_is_int_elim_to_real => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal []
  | Eo.CRule.arith_div_int_to_real => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal []
  | Eo.CRule.arith_div_total_int_to_real => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal []
  | Eo.CRule.arith_mod_over_mod_1 => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 []
  | Eo.CRule.arith_mod_over_mod => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod []
  | Eo.CRule.arith_mod_over_mod_mult => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult []
  | Eo.CRule.arith_int_eq_conflict => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict []
  | Eo.CRule.arith_int_geq_tighten => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten []
  | Eo.CRule.arith_divisible_elim => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim []
  | Eo.CRule.arith_abs_eq => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq []
  | Eo.CRule.arith_abs_int_gt => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt []
  | Eo.CRule.arith_abs_real_gt => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt []
  | Eo.CRule.arith_geq_ite_lift => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift []
  | Eo.CRule.arith_leq_ite_lift => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift []
  | Eo.CRule.arith_min_lt1 => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 []
  | Eo.CRule.arith_min_lt2 => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 []
  | Eo.CRule.arith_max_geq1 => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 []
  | Eo.CRule.arith_max_geq2 => Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 []
  | Eo.CRule.array_read_over_write => Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite []
  | Eo.CRule.array_read_over_write2 => Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 []
  | Eo.CRule.array_store_overwrite => Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite []
  | Eo.CRule.array_store_self => Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself []
  | Eo.CRule.array_read_over_write_split => Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit []
  | Eo.CRule.array_store_swap => Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap []
  | Eo.CRule.bool_double_not_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim []
  | Eo.CRule.bool_not_true => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue []
  | Eo.CRule.bool_not_false => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse []
  | Eo.CRule.bool_eq_true => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue []
  | Eo.CRule.bool_eq_false => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse []
  | Eo.CRule.bool_eq_nrefl => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl []
  | Eo.CRule.bool_impl_false1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 []
  | Eo.CRule.bool_impl_false2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 []
  | Eo.CRule.bool_impl_true1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 []
  | Eo.CRule.bool_impl_true2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 []
  | Eo.CRule.bool_impl_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim []
  | Eo.CRule.bool_dual_impl_eq => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq []
  | Eo.CRule.bool_and_conf => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf []
  | Eo.CRule.bool_and_conf2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 []
  | Eo.CRule.bool_or_taut => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut []
  | Eo.CRule.bool_or_taut2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 []
  | Eo.CRule.bool_or_de_morgan => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan []
  | Eo.CRule.bool_implies_de_morgan => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan []
  | Eo.CRule.bool_and_de_morgan => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan []
  | Eo.CRule.bool_or_and_distrib => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib []
  | Eo.CRule.bool_implies_or_distrib => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib []
  | Eo.CRule.bool_xor_refl => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl []
  | Eo.CRule.bool_xor_nrefl => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl []
  | Eo.CRule.bool_xor_false => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse []
  | Eo.CRule.bool_xor_true => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue []
  | Eo.CRule.bool_xor_comm => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm []
  | Eo.CRule.bool_xor_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim []
  | Eo.CRule.bool_not_xor_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim []
  | Eo.CRule.bool_not_eq_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 []
  | Eo.CRule.bool_not_eq_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 []
  | Eo.CRule.ite_neg_branch => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch []
  | Eo.CRule.ite_then_true => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue []
  | Eo.CRule.ite_else_false => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse []
  | Eo.CRule.ite_then_false => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse []
  | Eo.CRule.ite_else_true => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue []
  | Eo.CRule.ite_then_lookahead_self => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself []
  | Eo.CRule.ite_else_lookahead_self => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself []
  | Eo.CRule.ite_then_lookahead_not_self => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself []
  | Eo.CRule.ite_else_lookahead_not_self => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself []
  | Eo.CRule.ite_expand => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fexpand []
  | Eo.CRule.bool_not_ite_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim []
  | Eo.CRule.ite_true_cond => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond []
  | Eo.CRule.ite_false_cond => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond []
  | Eo.CRule.ite_not_cond => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond []
  | Eo.CRule.ite_eq_branch => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch []
  | Eo.CRule.ite_then_lookahead => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead []
  | Eo.CRule.ite_else_lookahead => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead []
  | Eo.CRule.ite_then_neg_lookahead => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead []
  | Eo.CRule.ite_else_neg_lookahead => Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead []
  | Eo.CRule.bv_concat_extract_merge => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge []
  | Eo.CRule.bv_extract_extract => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract []
  | Eo.CRule.bv_extract_whole => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole []
  | Eo.CRule.bv_extract_concat_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 []
  | Eo.CRule.bv_extract_concat_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 []
  | Eo.CRule.bv_extract_concat_3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 []
  | Eo.CRule.bv_extract_concat_4 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 []
  | Eo.CRule.bv_eq_extract_elim1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 []
  | Eo.CRule.bv_eq_extract_elim2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 []
  | Eo.CRule.bv_eq_extract_elim3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 []
  | Eo.CRule.bv_extract_not => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot []
  | Eo.CRule.bv_extract_sign_extend_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 []
  | Eo.CRule.bv_extract_sign_extend_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 []
  | Eo.CRule.bv_extract_sign_extend_3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 []
  | Eo.CRule.bv_not_xor => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor []
  | Eo.CRule.bv_and_simplify_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 []
  | Eo.CRule.bv_and_simplify_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 []
  | Eo.CRule.bv_or_simplify_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 []
  | Eo.CRule.bv_or_simplify_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 []
  | Eo.CRule.bv_xor_simplify_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 []
  | Eo.CRule.bv_xor_simplify_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 []
  | Eo.CRule.bv_xor_simplify_3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 []
  | Eo.CRule.bv_ult_add_one => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone []
  | Eo.CRule.bv_mult_slt_mult_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 []
  | Eo.CRule.bv_mult_slt_mult_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 []
  | Eo.CRule.bv_commutative_xor => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor []
  | Eo.CRule.bv_commutative_comp => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp []
  | Eo.CRule.bv_zero_extend_eliminate_0 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 []
  | Eo.CRule.bv_sign_extend_eliminate_0 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 []
  | Eo.CRule.bv_not_neq => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq []
  | Eo.CRule.bv_ult_ones => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones []
  | Eo.CRule.bv_concat_merge_const => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst []
  | Eo.CRule.bv_commutative_add => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd []
  | Eo.CRule.bv_sub_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate []
  | Eo.CRule.bv_ite_width_one => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone []
  | Eo.CRule.bv_ite_width_one_not => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot []
  | Eo.CRule.bv_eq_xor_solve => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve []
  | Eo.CRule.bv_eq_not_solve => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve []
  | Eo.CRule.bv_ugt_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate []
  | Eo.CRule.bv_uge_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate []
  | Eo.CRule.bv_sgt_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate []
  | Eo.CRule.bv_sge_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate []
  | Eo.CRule.bv_sle_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate []
  | Eo.CRule.bv_redor_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate []
  | Eo.CRule.bv_redand_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate []
  | Eo.CRule.bv_ule_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate []
  | Eo.CRule.bv_comp_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate []
  | Eo.CRule.bv_rotate_left_eliminate_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 []
  | Eo.CRule.bv_rotate_left_eliminate_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 []
  | Eo.CRule.bv_rotate_right_eliminate_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 []
  | Eo.CRule.bv_rotate_right_eliminate_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 []
  | Eo.CRule.bv_nand_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate []
  | Eo.CRule.bv_nor_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate []
  | Eo.CRule.bv_xnor_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate []
  | Eo.CRule.bv_sdiv_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate []
  | Eo.CRule.bv_zero_extend_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate []
  | Eo.CRule.bv_uaddo_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate []
  | Eo.CRule.bv_saddo_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate []
  | Eo.CRule.bv_sdivo_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate []
  | Eo.CRule.bv_smod_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate []
  | Eo.CRule.bv_srem_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate []
  | Eo.CRule.bv_usubo_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate []
  | Eo.CRule.bv_ssubo_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate []
  | Eo.CRule.bv_nego_eliminate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate []
  | Eo.CRule.bv_ite_equal_children => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren []
  | Eo.CRule.bv_ite_const_cond_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 []
  | Eo.CRule.bv_ite_const_cond_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 []
  | Eo.CRule.bv_ite_const_children_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 []
  | Eo.CRule.bv_ite_const_children_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 []
  | Eo.CRule.bv_ite_equal_cond_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 []
  | Eo.CRule.bv_ite_equal_cond_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 []
  | Eo.CRule.bv_ite_equal_cond_3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 []
  | Eo.CRule.bv_ite_merge_then_if => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif []
  | Eo.CRule.bv_ite_merge_else_if => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif []
  | Eo.CRule.bv_ite_merge_then_else => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse []
  | Eo.CRule.bv_ite_merge_else_else => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse []
  | Eo.CRule.bv_shl_by_const_0 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 []
  | Eo.CRule.bv_shl_by_const_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 []
  | Eo.CRule.bv_shl_by_const_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 []
  | Eo.CRule.bv_lshr_by_const_0 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 []
  | Eo.CRule.bv_lshr_by_const_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 []
  | Eo.CRule.bv_lshr_by_const_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 []
  | Eo.CRule.bv_ashr_by_const_0 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 []
  | Eo.CRule.bv_ashr_by_const_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 []
  | Eo.CRule.bv_ashr_by_const_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 []
  | Eo.CRule.bv_and_concat_pullup => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup []
  | Eo.CRule.bv_or_concat_pullup => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup []
  | Eo.CRule.bv_xor_concat_pullup => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup []
  | Eo.CRule.bv_and_concat_pullup2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 []
  | Eo.CRule.bv_or_concat_pullup2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 []
  | Eo.CRule.bv_xor_concat_pullup2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 []
  | Eo.CRule.bv_and_concat_pullup3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 []
  | Eo.CRule.bv_or_concat_pullup3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 []
  | Eo.CRule.bv_xor_concat_pullup3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 []
  | Eo.CRule.bv_xor_duplicate => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate []
  | Eo.CRule.bv_xor_ones => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones []
  | Eo.CRule.bv_xor_not => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot []
  | Eo.CRule.bv_not_idemp => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp []
  | Eo.CRule.bv_ult_zero_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 []
  | Eo.CRule.bv_ult_zero_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 []
  | Eo.CRule.bv_ult_self => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself []
  | Eo.CRule.bv_lt_self => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself []
  | Eo.CRule.bv_ule_self => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself []
  | Eo.CRule.bv_ule_zero => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero []
  | Eo.CRule.bv_zero_ule => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule []
  | Eo.CRule.bv_sle_self => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself []
  | Eo.CRule.bv_ule_max => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax []
  | Eo.CRule.bv_not_ult => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult []
  | Eo.CRule.bv_mult_pow2_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 []
  | Eo.CRule.bv_mult_pow2_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 []
  | Eo.CRule.bv_mult_pow2_2b => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b []
  | Eo.CRule.bv_extract_mult_leading_bit => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit []
  | Eo.CRule.bv_udiv_pow2_not_one => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone []
  | Eo.CRule.bv_udiv_zero => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero []
  | Eo.CRule.bv_udiv_one => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone []
  | Eo.CRule.bv_urem_pow2_not_one => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone []
  | Eo.CRule.bv_urem_one => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone []
  | Eo.CRule.bv_urem_self => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself []
  | Eo.CRule.bv_shl_zero => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero []
  | Eo.CRule.bv_lshr_zero => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero []
  | Eo.CRule.bv_ashr_zero => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero []
  | Eo.CRule.bv_ugt_urem => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem []
  | Eo.CRule.bv_ult_one => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone []
  | Eo.CRule.bv_merge_sign_extend_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 []
  | Eo.CRule.bv_merge_sign_extend_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 []
  | Eo.CRule.bv_sign_extend_eq_const_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 []
  | Eo.CRule.bv_sign_extend_eq_const_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 []
  | Eo.CRule.bv_zero_extend_eq_const_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 []
  | Eo.CRule.bv_zero_extend_eq_const_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 []
  | Eo.CRule.bv_zero_extend_ult_const_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 []
  | Eo.CRule.bv_zero_extend_ult_const_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 []
  | Eo.CRule.bv_sign_extend_ult_const_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 []
  | Eo.CRule.bv_sign_extend_ult_const_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 []
  | Eo.CRule.bv_sign_extend_ult_const_3 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 []
  | Eo.CRule.bv_sign_extend_ult_const_4 => Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 []
  | Eo.CRule.sets_eq_singleton_emp => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp []
  | Eo.CRule.sets_member_singleton => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton []
  | Eo.CRule.sets_member_emp => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp []
  | Eo.CRule.sets_subset_elim => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim []
  | Eo.CRule.sets_insert_elim => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim []
  | Eo.CRule.sets_union_comm => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm []
  | Eo.CRule.sets_inter_comm => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm []
  | Eo.CRule.sets_inter_emp1 => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 []
  | Eo.CRule.sets_inter_emp2 => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 []
  | Eo.CRule.sets_minus_emp1 => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 []
  | Eo.CRule.sets_minus_emp2 => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 []
  | Eo.CRule.sets_union_emp1 => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 []
  | Eo.CRule.sets_union_emp2 => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 []
  | Eo.CRule.sets_inter_member => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember []
  | Eo.CRule.sets_minus_member => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember []
  | Eo.CRule.sets_union_member => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember []
  | Eo.CRule.sets_choose_singleton => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton []
  | Eo.CRule.sets_minus_self => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself []
  | Eo.CRule.sets_union_self => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself []
  | Eo.CRule.sets_inter_self => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself []
  | Eo.CRule.sets_is_empty_elim => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim []
  | Eo.CRule.sets_is_singleton_elim => Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim []
  | Eo.CRule.str_eq_ctn_false => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse []
  | Eo.CRule.str_eq_ctn_full_false1 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 []
  | Eo.CRule.str_eq_ctn_full_false2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 []
  | Eo.CRule.str_eq_len_false => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse []
  | Eo.CRule.str_substr_empty_str => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr []
  | Eo.CRule.str_substr_empty_range => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange []
  | Eo.CRule.str_substr_empty_start => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart []
  | Eo.CRule.str_substr_empty_start_neg => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg []
  | Eo.CRule.str_substr_substr_start_geq_len => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen []
  | Eo.CRule.str_substr_eq_empty => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty []
  | Eo.CRule.str_substr_z_eq_empty_leq => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq []
  | Eo.CRule.str_substr_eq_empty_leq_len => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen []
  | Eo.CRule.str_len_replace_inv => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv []
  | Eo.CRule.str_len_replace_all_inv => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv []
  | Eo.CRule.str_len_update_inv => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv []
  | Eo.CRule.str_update_oob => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob []
  | Eo.CRule.str_update_rev => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev []
  | Eo.CRule.str_update_fit => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit []
  | Eo.CRule.str_update_concat_fit0 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 []
  | Eo.CRule.str_update_concat_fit => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit []
  | Eo.CRule.str_update_in_first_concat => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat []
  | Eo.CRule.str_len_substr_in_range => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange []
  | Eo.CRule.str_concat_clash => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash []
  | Eo.CRule.str_concat_clash_rev => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev []
  | Eo.CRule.str_concat_clash2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 []
  | Eo.CRule.str_concat_clash2_rev => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev []
  | Eo.CRule.str_concat_unify => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify []
  | Eo.CRule.str_concat_unify_rev => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev []
  | Eo.CRule.str_concat_unify_base => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase []
  | Eo.CRule.str_concat_unify_base_rev => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev []
  | Eo.CRule.str_prefixof_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim []
  | Eo.CRule.str_suffixof_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim []
  | Eo.CRule.str_prefixof_eq => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq []
  | Eo.CRule.str_suffixof_eq => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq []
  | Eo.CRule.str_prefixof_one => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone []
  | Eo.CRule.str_suffixof_one => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone []
  | Eo.CRule.str_substr_combine1 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 []
  | Eo.CRule.str_substr_combine2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 []
  | Eo.CRule.str_substr_combine3 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 []
  | Eo.CRule.str_substr_combine4 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 []
  | Eo.CRule.str_substr_concat1 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 []
  | Eo.CRule.str_substr_concat2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 []
  | Eo.CRule.str_substr_replace => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace []
  | Eo.CRule.str_substr_full => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull []
  | Eo.CRule.str_substr_full_eq => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq []
  | Eo.CRule.str_contains_refl => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl []
  | Eo.CRule.str_contains_concat_find => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind []
  | Eo.CRule.str_contains_concat_find_contra => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra []
  | Eo.CRule.str_contains_split_char => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar []
  | Eo.CRule.str_contains_leq_len_eq => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq []
  | Eo.CRule.str_contains_emp => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp []
  | Eo.CRule.str_contains_char => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar []
  | Eo.CRule.str_at_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim []
  | Eo.CRule.str_replace_self => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself []
  | Eo.CRule.str_replace_id => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid []
  | Eo.CRule.str_replace_prefix => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix []
  | Eo.CRule.str_replace_prefix_concat => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat []
  | Eo.CRule.str_replace_no_contains => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains []
  | Eo.CRule.str_replace_find_base => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase []
  | Eo.CRule.str_replace_find_first_concat => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat []
  | Eo.CRule.str_replace_empty => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty []
  | Eo.CRule.str_replace_one_pre => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre []
  | Eo.CRule.str_replace_find_pre => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre []
  | Eo.CRule.str_replace_all_no_contains => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains []
  | Eo.CRule.str_replace_all_find_pre => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre []
  | Eo.CRule.str_replace_all_find => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind []
  | Eo.CRule.str_replace_all_empty => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty []
  | Eo.CRule.str_replace_all_id => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid []
  | Eo.CRule.str_replace_all_self => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself []
  | Eo.CRule.str_replace_re_none => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone []
  | Eo.CRule.str_replace_re_all_none => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone []
  | Eo.CRule.str_len_concat_rec => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec []
  | Eo.CRule.str_len_eq_zero_concat_rec => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec []
  | Eo.CRule.str_len_eq_zero_base => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase []
  | Eo.CRule.str_indexof_self => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself []
  | Eo.CRule.str_indexof_no_contains => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains []
  | Eo.CRule.str_indexof_oob => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob []
  | Eo.CRule.str_indexof_oob2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 []
  | Eo.CRule.str_indexof_contains_pre => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre []
  | Eo.CRule.str_indexof_contains_concat_pre => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre []
  | Eo.CRule.str_indexof_prefix_concat => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat []
  | Eo.CRule.str_indexof_len_oob => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob []
  | Eo.CRule.str_indexof_len_oob2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 []
  | Eo.CRule.str_indexof_find_emp => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp []
  | Eo.CRule.str_indexof_eq_irr => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr []
  | Eo.CRule.str_indexof_re_none => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone []
  | Eo.CRule.str_indexof_re_emp_re => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre []
  | Eo.CRule.str_to_lower_concat => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat []
  | Eo.CRule.str_to_upper_concat => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat []
  | Eo.CRule.str_to_lower_upper => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper []
  | Eo.CRule.str_to_lower_idem => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem []
  | Eo.CRule.str_to_upper_lower => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower []
  | Eo.CRule.str_to_upper_idem => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem []
  | Eo.CRule.str_to_lower_len => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen []
  | Eo.CRule.str_to_upper_len => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen []
  | Eo.CRule.str_to_lower_from_int => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint []
  | Eo.CRule.str_to_upper_from_int => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint []
  | Eo.CRule.str_to_int_concat_neg_one => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone []
  | Eo.CRule.str_is_digit_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim []
  | Eo.CRule.str_leq_empty => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty []
  | Eo.CRule.str_leq_empty_eq => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq []
  | Eo.CRule.str_leq_concat_false => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse []
  | Eo.CRule.str_leq_concat_true => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue []
  | Eo.CRule.str_leq_concat_base_1 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 []
  | Eo.CRule.str_leq_concat_base_2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 []
  | Eo.CRule.str_lt_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim []
  | Eo.CRule.str_from_int_no_ctn_nondigit => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit []
  | Eo.CRule.str_substr_ctn_contra => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra []
  | Eo.CRule.str_substr_ctn => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn []
  | Eo.CRule.str_replace_dual_ctn => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn []
  | Eo.CRule.str_replace_dual_ctn_false => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse []
  | Eo.CRule.str_replace_self_ctn_simp => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp []
  | Eo.CRule.str_replace_emp_ctn_src => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc []
  | Eo.CRule.str_substr_char_start_eq_len => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen []
  | Eo.CRule.str_contains_repl_char => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar []
  | Eo.CRule.str_contains_repl_self_tgt_char => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar []
  | Eo.CRule.str_contains_repl_self => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself []
  | Eo.CRule.str_contains_repl_tgt => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt []
  | Eo.CRule.str_repl_repl_len_id => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid []
  | Eo.CRule.str_repl_repl_src_tgt_no_ctn => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn []
  | Eo.CRule.str_repl_repl_tgt_self => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself []
  | Eo.CRule.str_repl_repl_tgt_no_ctn => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn []
  | Eo.CRule.str_repl_repl_src_self => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself []
  | Eo.CRule.str_repl_repl_src_inv_no_ctn1 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 []
  | Eo.CRule.str_repl_repl_src_inv_no_ctn2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 []
  | Eo.CRule.str_repl_repl_src_inv_no_ctn3 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 []
  | Eo.CRule.str_repl_repl_dual_self => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself []
  | Eo.CRule.str_repl_repl_dual_ite1 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 []
  | Eo.CRule.str_repl_repl_dual_ite2 => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 []
  | Eo.CRule.str_repl_repl_lookahead_id_simp => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp []
  | Eo.CRule.re_all_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim []
  | Eo.CRule.re_opt_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim []
  | Eo.CRule.re_diff_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim []
  | Eo.CRule.re_plus_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim []
  | Eo.CRule.re_repeat_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim []
  | Eo.CRule.re_concat_star_swap => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap []
  | Eo.CRule.re_concat_star_repeat => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat []
  | Eo.CRule.re_concat_star_nullable1 => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 []
  | Eo.CRule.re_concat_star_nullable2 => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 []
  | Eo.CRule.re_concat_merge => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge []
  | Eo.CRule.re_union_all => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall []
  | Eo.CRule.re_union_const_elim => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim []
  | Eo.CRule.re_inter_all => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall []
  | Eo.CRule.re_star_none => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone []
  | Eo.CRule.re_star_emp => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp []
  | Eo.CRule.re_star_star => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar []
  | Eo.CRule.re_range_refl => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl []
  | Eo.CRule.re_range_emp => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp []
  | Eo.CRule.re_range_non_singleton_1 => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 []
  | Eo.CRule.re_range_non_singleton_2 => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 []
  | Eo.CRule.re_star_union_char => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar []
  | Eo.CRule.re_star_union_drop_emp => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp []
  | Eo.CRule.re_loop_neg => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg []
  | Eo.CRule.re_loop_star => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar []
  | Eo.CRule.re_inter_cstring => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring []
  | Eo.CRule.re_inter_cstring_neg => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg []
  | Eo.CRule.str_substr_len_include => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude []
  | Eo.CRule.str_substr_len_include_pre => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre []
  | Eo.CRule.str_substr_len_norm => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm []
  | Eo.CRule.seq_len_rev => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev []
  | Eo.CRule.seq_rev_rev => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev []
  | Eo.CRule.seq_rev_concat => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat []
  | Eo.CRule.str_eq_repl_self_emp => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp []
  | Eo.CRule.str_eq_repl_no_change => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange []
  | Eo.CRule.str_eq_repl_tgt_eq_len => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen []
  | Eo.CRule.str_eq_repl_len_one_emp_prefix => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix []
  | Eo.CRule.str_eq_repl_emp_tgt_nemp => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp []
  | Eo.CRule.str_eq_repl_nemp_src_emp => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp []
  | Eo.CRule.str_eq_repl_self_src => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc []
  | Eo.CRule.seq_len_unit => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit []
  | Eo.CRule.seq_nth_unit => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit []
  | Eo.CRule.seq_nth_concat_unit => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit []
  | Eo.CRule.seq_nth_concat_unit_gen => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen []
  | Eo.CRule.seq_rev_unit => Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit []
  | Eo.CRule.re_in_empty => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty []
  | Eo.CRule.re_in_sigma => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma []
  | Eo.CRule.re_in_sigma_star => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar []
  | Eo.CRule.re_in_cstring => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring []
  | Eo.CRule.re_in_comp => Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp []
  | Eo.CRule.str_in_re_union_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim []
  | Eo.CRule.str_in_re_inter_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim []
  | Eo.CRule.str_in_re_range_elim => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim []
  | Eo.CRule.str_in_re_contains => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains []
  | Eo.CRule.str_in_re_from_int_nemp_dig_range => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange []
  | Eo.CRule.str_in_re_from_int_dig_range => Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange []
  | Eo.CRule.eq_refl => Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5frefl []
  | Eo.CRule.eq_symm => Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fsymm []
  | Eo.CRule.eq_cond_deq => Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq []
  | Eo.CRule.eq_ite_lift => Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift []
  | Eo.CRule.distinct_binary_elim => Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim []
  | Eo.CRule.uf_bv2nat_int2bv => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv []
  | Eo.CRule.uf_bv2nat_int2bv_extend => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend []
  | Eo.CRule.uf_bv2nat_int2bv_extract => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract []
  | Eo.CRule.uf_int2bv_bv2nat => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat []
  | Eo.CRule.uf_bv2nat_geq_elim => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim []
  | Eo.CRule.uf_int2bv_bvult_equiv => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv []
  | Eo.CRule.uf_int2bv_bvule_equiv => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv []
  | Eo.CRule.uf_sbv_to_int_elim => Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim []
  | Eo.CRule.evaluate => Tree.node schema.Constructor.eo__24emb_5fr_2eevaluate []
  | Eo.CRule.distinct_values => Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues []
  | Eo.CRule.aci_norm => Tree.node schema.Constructor.eo__24emb_5fr_2eaci_5fnorm []
  | Eo.CRule.absorb => Tree.node schema.Constructor.eo__24emb_5fr_2eabsorb []
  | Eo.CRule.distinct_card_conflict => Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict []
end

mutual
/-- The `CRule` that a tree stands for. -/
def dec_CRule : Tree → Option Eo.CRule
  | Tree.node schema.Constructor.eo__24emb_5fr_2escope [] => some Eo.CRule.scope
  | Tree.node schema.Constructor.eo__24emb_5fr_2eprocess_5fscope [] => some Eo.CRule.process_scope
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq [] => some Eo.CRule.ite_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2esplit [] => some Eo.CRule.split
  | Tree.node schema.Constructor.eo__24emb_5fr_2eresolution [] => some Eo.CRule.resolution
  | Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fresolution [] => some Eo.CRule.chain_resolution
  | Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution [] => some Eo.CRule.chain_m_resolution
  | Tree.node schema.Constructor.eo__24emb_5fr_2efactoring [] => some Eo.CRule.factoring
  | Tree.node schema.Constructor.eo__24emb_5fr_2ereordering [] => some Eo.CRule.reordering
  | Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fresolve [] => some Eo.CRule.eq_resolve
  | Tree.node schema.Constructor.eo__24emb_5fr_2emodus_5fponens [] => some Eo.CRule.modus_ponens
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim [] => some Eo.CRule.not_not_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2econtra [] => some Eo.CRule.contra
  | Tree.node schema.Constructor.eo__24emb_5fr_2eand_5felim [] => some Eo.CRule.and_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2eand_5fintro [] => some Eo.CRule.and_intro
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5for_5felim [] => some Eo.CRule.not_or_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2eimplies_5felim [] => some Eo.CRule.implies_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 [] => some Eo.CRule.not_implies_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 [] => some Eo.CRule.not_implies_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 [] => some Eo.CRule.equiv_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 [] => some Eo.CRule.equiv_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 [] => some Eo.CRule.not_equiv_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 [] => some Eo.CRule.not_equiv_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim1 [] => some Eo.CRule.xor_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim2 [] => some Eo.CRule.xor_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 [] => some Eo.CRule.not_xor_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 [] => some Eo.CRule.not_xor_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim1 [] => some Eo.CRule.ite_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim2 [] => some Eo.CRule.ite_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 [] => some Eo.CRule.not_ite_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 [] => some Eo.CRule.not_ite_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fand [] => some Eo.CRule.not_and
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos [] => some Eo.CRule.cnf_and_pos
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg [] => some Eo.CRule.cnf_and_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos [] => some Eo.CRule.cnf_or_pos
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg [] => some Eo.CRule.cnf_or_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos [] => some Eo.CRule.cnf_implies_pos
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 [] => some Eo.CRule.cnf_implies_neg1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 [] => some Eo.CRule.cnf_implies_neg2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 [] => some Eo.CRule.cnf_equiv_pos1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 [] => some Eo.CRule.cnf_equiv_pos2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 [] => some Eo.CRule.cnf_equiv_neg1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 [] => some Eo.CRule.cnf_equiv_neg2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 [] => some Eo.CRule.cnf_xor_pos1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 [] => some Eo.CRule.cnf_xor_pos2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 [] => some Eo.CRule.cnf_xor_neg1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 [] => some Eo.CRule.cnf_xor_neg2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 [] => some Eo.CRule.cnf_ite_pos1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 [] => some Eo.CRule.cnf_ite_pos2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 [] => some Eo.CRule.cnf_ite_pos3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 [] => some Eo.CRule.cnf_ite_neg1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 [] => some Eo.CRule.cnf_ite_neg2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 [] => some Eo.CRule.cnf_ite_neg3
  | Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite [] => some Eo.CRule.arrays_read_over_write
  | Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra [] => some Eo.CRule.arrays_read_over_write_contra
  | Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 [] => some Eo.CRule.arrays_read_over_write_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fext [] => some Eo.CRule.arrays_ext
  | Tree.node schema.Constructor.eo__24emb_5fr_2erefl [] => some Eo.CRule.refl
  | Tree.node schema.Constructor.eo__24emb_5fr_2esymm [] => some Eo.CRule.symm
  | Tree.node schema.Constructor.eo__24emb_5fr_2etrans [] => some Eo.CRule.trans
  | Tree.node schema.Constructor.eo__24emb_5fr_2econg [] => some Eo.CRule.cong
  | Tree.node schema.Constructor.eo__24emb_5fr_2enary_5fcong [] => some Eo.CRule.nary_cong
  | Tree.node schema.Constructor.eo__24emb_5fr_2epairwise_5fcong [] => some Eo.CRule.pairwise_cong
  | Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5fintro [] => some Eo.CRule.true_intro
  | Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5felim [] => some Eo.CRule.true_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5fintro [] => some Eo.CRule.false_intro
  | Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5felim [] => some Eo.CRule.false_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2eho_5fcong [] => some Eo.CRule.ho_cong
  | Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5felim [] => some Eo.CRule.distinct_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue [] => some Eo.CRule.distinct_true
  | Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse [] => some Eo.CRule.distinct_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub [] => some Eo.CRule.arith_sum_ub
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos [] => some Eo.CRule.arith_mult_pos
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg [] => some Eo.CRule.arith_mult_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy [] => some Eo.CRule.arith_trichotomy
  | Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub [] => some Eo.CRule.int_tight_ub
  | Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb [] => some Eo.CRule.int_tight_lb
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent [] => some Eo.CRule.arith_mult_tangent
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign [] => some Eo.CRule.arith_mult_sign
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison [] => some Eo.CRule.arith_mult_abs_comparison
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5freduction [] => some Eo.CRule.arith_reduction
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm [] => some Eo.CRule.arith_poly_norm
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel [] => some Eo.CRule.arith_poly_norm_rel
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim [] => some Eo.CRule.bv_repeat_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim [] => some Eo.CRule.bv_smulo_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim [] => some Eo.CRule.bv_umulo_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing [] => some Eo.CRule.bv_bitwise_slicing
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep [] => some Eo.CRule.bv_bitblast_step
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm [] => some Eo.CRule.bv_poly_norm
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq [] => some Eo.CRule.bv_poly_norm_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos [] => some Eo.CRule.string_length_pos
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty [] => some Eo.CRule.string_length_non_empty
  | Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5feq [] => some Eo.CRule.concat_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5funify [] => some Eo.CRule.concat_unify
  | Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit [] => some Eo.CRule.concat_csplit
  | Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fsplit [] => some Eo.CRule.concat_split
  | Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5flprop [] => some Eo.CRule.concat_lprop
  | Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcprop [] => some Eo.CRule.concat_cprop
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fdecompose [] => some Eo.CRule.string_decompose
  | Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength [] => some Eo.CRule.exists_string_length
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj [] => some Eo.CRule.string_code_inj
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj [] => some Eo.CRule.string_seq_unit_inj
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter [] => some Eo.CRule.re_inter
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat [] => some Eo.CRule.re_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos [] => some Eo.CRule.re_unfold_pos
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed [] => some Eo.CRule.re_unfold_neg_concat_fixed
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg [] => some Eo.CRule.re_unfold_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fext [] => some Eo.CRule.string_ext
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5freduction [] => some Eo.CRule.string_reduction
  | Tree.node schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction [] => some Eo.CRule.string_eager_reduction
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail [] => some Eo.CRule.arith_string_pred_entail
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox [] => some Eo.CRule.arith_string_pred_safe_approx
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval [] => some Eo.CRule.str_in_re_eval
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume [] => some Eo.CRule.str_in_re_consume
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim [] => some Eo.CRule.re_loop_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim [] => some Eo.CRule.re_eq_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion [] => some Eo.CRule.re_inter_inclusion
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion [] => some Eo.CRule.re_union_inclusion
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar [] => some Eo.CRule.str_in_re_concat_star_char
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma [] => some Eo.CRule.str_in_re_sigma
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar [] => some Eo.CRule.str_in_re_sigma_star
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset [] => some Eo.CRule.str_ctn_multiset_subset
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn [] => some Eo.CRule.str_overlap_split_ctn
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn [] => some Eo.CRule.str_overlap_endpoints_ctn
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof [] => some Eo.CRule.str_overlap_endpoints_indexof
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace [] => some Eo.CRule.str_overlap_endpoints_replace
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval [] => some Eo.CRule.str_indexof_re_eval
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval [] => some Eo.CRule.str_replace_re_eval
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval [] => some Eo.CRule.str_replace_re_all_eval
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop [] => some Eo.CRule.seq_eval_op
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj [] => some Eo.CRule.sets_singleton_inj
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fext [] => some Eo.CRule.sets_ext
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember [] => some Eo.CRule.sets_choose_member
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop [] => some Eo.CRule.sets_eval_op
  | Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange [] => some Eo.CRule.ubv_to_int_range
  | Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim [] => some Eo.CRule.ubv_to_int_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim [] => some Eo.CRule.int_to_bv_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2einstantiate [] => some Eo.CRule.instantiate
  | Tree.node schema.Constructor.eo__24emb_5fr_2eskolemize [] => some Eo.CRule.skolemize
  | Tree.node schema.Constructor.eo__24emb_5fr_2eskolem_5fintro [] => some Eo.CRule.skolem_intro
  | Tree.node schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv [] => some Eo.CRule.alpha_equiv
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebeta_5freduce [] => some Eo.CRule.beta_reduce
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering [] => some Eo.CRule.quant_var_reordering
  | Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5felim [] => some Eo.CRule.exists_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars [] => some Eo.CRule.quant_unused_vars
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex [] => some Eo.CRule.quant_merge_prenex
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand [] => some Eo.CRule.quant_miniscope_and
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for [] => some Eo.CRule.quant_miniscope_or
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite [] => some Eo.CRule.quant_miniscope_ite
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq [] => some Eo.CRule.quant_var_elim_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit [] => some Eo.CRule.quant_dt_split
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fsplit [] => some Eo.CRule.dt_split
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5finst [] => some Eo.CRule.dt_inst
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector [] => some Eo.CRule.dt_collapse_selector
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester [] => some Eo.CRule.dt_collapse_tester
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton [] => some Eo.CRule.dt_collapse_tester_singleton
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq [] => some Eo.CRule.dt_cons_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash [] => some Eo.CRule.dt_cons_eq_clash
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcycle [] => some Eo.CRule.dt_cycle
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater [] => some Eo.CRule.dt_collapse_updater
  | Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim [] => some Eo.CRule.dt_updater_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal [] => some Eo.CRule.arith_div_total_zero_real
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint [] => some Eo.CRule.arith_div_total_zero_int
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal [] => some Eo.CRule.arith_int_div_total
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone [] => some Eo.CRule.arith_int_div_total_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero [] => some Eo.CRule.arith_int_div_total_zero
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg [] => some Eo.CRule.arith_int_div_total_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal [] => some Eo.CRule.arith_int_mod_total
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone [] => some Eo.CRule.arith_int_mod_total_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero [] => some Eo.CRule.arith_int_mod_total_zero
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg [] => some Eo.CRule.arith_int_mod_total_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod [] => some Eo.CRule.arith_int_div_total_over_mod
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt [] => some Eo.CRule.arith_elim_gt
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt [] => some Eo.CRule.arith_elim_lt
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt [] => some Eo.CRule.arith_elim_int_gt
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt [] => some Eo.CRule.arith_elim_int_lt
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq [] => some Eo.CRule.arith_elim_leq
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm [] => some Eo.CRule.arith_leq_norm
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten [] => some Eo.CRule.arith_geq_tighten
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint [] => some Eo.CRule.arith_geq_norm1_int
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal [] => some Eo.CRule.arith_geq_norm1_real
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal [] => some Eo.CRule.arith_eq_elim_real
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint [] => some Eo.CRule.arith_eq_elim_int
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal [] => some Eo.CRule.arith_to_int_elim_to_real
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal [] => some Eo.CRule.arith_is_int_elim_to_real
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal [] => some Eo.CRule.arith_div_int_to_real
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal [] => some Eo.CRule.arith_div_total_int_to_real
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 [] => some Eo.CRule.arith_mod_over_mod_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod [] => some Eo.CRule.arith_mod_over_mod
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult [] => some Eo.CRule.arith_mod_over_mod_mult
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict [] => some Eo.CRule.arith_int_eq_conflict
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten [] => some Eo.CRule.arith_int_geq_tighten
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim [] => some Eo.CRule.arith_divisible_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq [] => some Eo.CRule.arith_abs_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt [] => some Eo.CRule.arith_abs_int_gt
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt [] => some Eo.CRule.arith_abs_real_gt
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift [] => some Eo.CRule.arith_geq_ite_lift
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift [] => some Eo.CRule.arith_leq_ite_lift
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 [] => some Eo.CRule.arith_min_lt1
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 [] => some Eo.CRule.arith_min_lt2
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 [] => some Eo.CRule.arith_max_geq1
  | Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 [] => some Eo.CRule.arith_max_geq2
  | Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite [] => some Eo.CRule.array_read_over_write
  | Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 [] => some Eo.CRule.array_read_over_write2
  | Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite [] => some Eo.CRule.array_store_overwrite
  | Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself [] => some Eo.CRule.array_store_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit [] => some Eo.CRule.array_read_over_write_split
  | Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap [] => some Eo.CRule.array_store_swap
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim [] => some Eo.CRule.bool_double_not_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue [] => some Eo.CRule.bool_not_true
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse [] => some Eo.CRule.bool_not_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue [] => some Eo.CRule.bool_eq_true
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse [] => some Eo.CRule.bool_eq_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl [] => some Eo.CRule.bool_eq_nrefl
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 [] => some Eo.CRule.bool_impl_false1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 [] => some Eo.CRule.bool_impl_false2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 [] => some Eo.CRule.bool_impl_true1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 [] => some Eo.CRule.bool_impl_true2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim [] => some Eo.CRule.bool_impl_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq [] => some Eo.CRule.bool_dual_impl_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf [] => some Eo.CRule.bool_and_conf
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 [] => some Eo.CRule.bool_and_conf2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut [] => some Eo.CRule.bool_or_taut
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 [] => some Eo.CRule.bool_or_taut2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan [] => some Eo.CRule.bool_or_de_morgan
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan [] => some Eo.CRule.bool_implies_de_morgan
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan [] => some Eo.CRule.bool_and_de_morgan
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib [] => some Eo.CRule.bool_or_and_distrib
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib [] => some Eo.CRule.bool_implies_or_distrib
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl [] => some Eo.CRule.bool_xor_refl
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl [] => some Eo.CRule.bool_xor_nrefl
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse [] => some Eo.CRule.bool_xor_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue [] => some Eo.CRule.bool_xor_true
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm [] => some Eo.CRule.bool_xor_comm
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim [] => some Eo.CRule.bool_xor_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim [] => some Eo.CRule.bool_not_xor_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 [] => some Eo.CRule.bool_not_eq_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 [] => some Eo.CRule.bool_not_eq_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch [] => some Eo.CRule.ite_neg_branch
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue [] => some Eo.CRule.ite_then_true
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse [] => some Eo.CRule.ite_else_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse [] => some Eo.CRule.ite_then_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue [] => some Eo.CRule.ite_else_true
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself [] => some Eo.CRule.ite_then_lookahead_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself [] => some Eo.CRule.ite_else_lookahead_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself [] => some Eo.CRule.ite_then_lookahead_not_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself [] => some Eo.CRule.ite_else_lookahead_not_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fexpand [] => some Eo.CRule.ite_expand
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim [] => some Eo.CRule.bool_not_ite_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond [] => some Eo.CRule.ite_true_cond
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond [] => some Eo.CRule.ite_false_cond
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond [] => some Eo.CRule.ite_not_cond
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch [] => some Eo.CRule.ite_eq_branch
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead [] => some Eo.CRule.ite_then_lookahead
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead [] => some Eo.CRule.ite_else_lookahead
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead [] => some Eo.CRule.ite_then_neg_lookahead
  | Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead [] => some Eo.CRule.ite_else_neg_lookahead
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge [] => some Eo.CRule.bv_concat_extract_merge
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract [] => some Eo.CRule.bv_extract_extract
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole [] => some Eo.CRule.bv_extract_whole
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 [] => some Eo.CRule.bv_extract_concat_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 [] => some Eo.CRule.bv_extract_concat_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 [] => some Eo.CRule.bv_extract_concat_3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 [] => some Eo.CRule.bv_extract_concat_4
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 [] => some Eo.CRule.bv_eq_extract_elim1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 [] => some Eo.CRule.bv_eq_extract_elim2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 [] => some Eo.CRule.bv_eq_extract_elim3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot [] => some Eo.CRule.bv_extract_not
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 [] => some Eo.CRule.bv_extract_sign_extend_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 [] => some Eo.CRule.bv_extract_sign_extend_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 [] => some Eo.CRule.bv_extract_sign_extend_3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor [] => some Eo.CRule.bv_not_xor
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 [] => some Eo.CRule.bv_and_simplify_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 [] => some Eo.CRule.bv_and_simplify_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 [] => some Eo.CRule.bv_or_simplify_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 [] => some Eo.CRule.bv_or_simplify_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 [] => some Eo.CRule.bv_xor_simplify_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 [] => some Eo.CRule.bv_xor_simplify_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 [] => some Eo.CRule.bv_xor_simplify_3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone [] => some Eo.CRule.bv_ult_add_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 [] => some Eo.CRule.bv_mult_slt_mult_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 [] => some Eo.CRule.bv_mult_slt_mult_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor [] => some Eo.CRule.bv_commutative_xor
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp [] => some Eo.CRule.bv_commutative_comp
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 [] => some Eo.CRule.bv_zero_extend_eliminate_0
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 [] => some Eo.CRule.bv_sign_extend_eliminate_0
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq [] => some Eo.CRule.bv_not_neq
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones [] => some Eo.CRule.bv_ult_ones
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst [] => some Eo.CRule.bv_concat_merge_const
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd [] => some Eo.CRule.bv_commutative_add
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate [] => some Eo.CRule.bv_sub_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone [] => some Eo.CRule.bv_ite_width_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot [] => some Eo.CRule.bv_ite_width_one_not
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve [] => some Eo.CRule.bv_eq_xor_solve
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve [] => some Eo.CRule.bv_eq_not_solve
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate [] => some Eo.CRule.bv_ugt_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate [] => some Eo.CRule.bv_uge_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate [] => some Eo.CRule.bv_sgt_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate [] => some Eo.CRule.bv_sge_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate [] => some Eo.CRule.bv_sle_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate [] => some Eo.CRule.bv_redor_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate [] => some Eo.CRule.bv_redand_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate [] => some Eo.CRule.bv_ule_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate [] => some Eo.CRule.bv_comp_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 [] => some Eo.CRule.bv_rotate_left_eliminate_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 [] => some Eo.CRule.bv_rotate_left_eliminate_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 [] => some Eo.CRule.bv_rotate_right_eliminate_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 [] => some Eo.CRule.bv_rotate_right_eliminate_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate [] => some Eo.CRule.bv_nand_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate [] => some Eo.CRule.bv_nor_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate [] => some Eo.CRule.bv_xnor_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate [] => some Eo.CRule.bv_sdiv_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate [] => some Eo.CRule.bv_zero_extend_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate [] => some Eo.CRule.bv_uaddo_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate [] => some Eo.CRule.bv_saddo_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate [] => some Eo.CRule.bv_sdivo_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate [] => some Eo.CRule.bv_smod_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate [] => some Eo.CRule.bv_srem_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate [] => some Eo.CRule.bv_usubo_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate [] => some Eo.CRule.bv_ssubo_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate [] => some Eo.CRule.bv_nego_eliminate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren [] => some Eo.CRule.bv_ite_equal_children
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 [] => some Eo.CRule.bv_ite_const_cond_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 [] => some Eo.CRule.bv_ite_const_cond_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 [] => some Eo.CRule.bv_ite_const_children_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 [] => some Eo.CRule.bv_ite_const_children_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 [] => some Eo.CRule.bv_ite_equal_cond_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 [] => some Eo.CRule.bv_ite_equal_cond_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 [] => some Eo.CRule.bv_ite_equal_cond_3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif [] => some Eo.CRule.bv_ite_merge_then_if
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif [] => some Eo.CRule.bv_ite_merge_else_if
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse [] => some Eo.CRule.bv_ite_merge_then_else
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse [] => some Eo.CRule.bv_ite_merge_else_else
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 [] => some Eo.CRule.bv_shl_by_const_0
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 [] => some Eo.CRule.bv_shl_by_const_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 [] => some Eo.CRule.bv_shl_by_const_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 [] => some Eo.CRule.bv_lshr_by_const_0
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 [] => some Eo.CRule.bv_lshr_by_const_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 [] => some Eo.CRule.bv_lshr_by_const_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 [] => some Eo.CRule.bv_ashr_by_const_0
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 [] => some Eo.CRule.bv_ashr_by_const_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 [] => some Eo.CRule.bv_ashr_by_const_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup [] => some Eo.CRule.bv_and_concat_pullup
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup [] => some Eo.CRule.bv_or_concat_pullup
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup [] => some Eo.CRule.bv_xor_concat_pullup
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 [] => some Eo.CRule.bv_and_concat_pullup2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 [] => some Eo.CRule.bv_or_concat_pullup2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 [] => some Eo.CRule.bv_xor_concat_pullup2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 [] => some Eo.CRule.bv_and_concat_pullup3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 [] => some Eo.CRule.bv_or_concat_pullup3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 [] => some Eo.CRule.bv_xor_concat_pullup3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate [] => some Eo.CRule.bv_xor_duplicate
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones [] => some Eo.CRule.bv_xor_ones
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot [] => some Eo.CRule.bv_xor_not
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp [] => some Eo.CRule.bv_not_idemp
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 [] => some Eo.CRule.bv_ult_zero_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 [] => some Eo.CRule.bv_ult_zero_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself [] => some Eo.CRule.bv_ult_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself [] => some Eo.CRule.bv_lt_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself [] => some Eo.CRule.bv_ule_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero [] => some Eo.CRule.bv_ule_zero
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule [] => some Eo.CRule.bv_zero_ule
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself [] => some Eo.CRule.bv_sle_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax [] => some Eo.CRule.bv_ule_max
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult [] => some Eo.CRule.bv_not_ult
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 [] => some Eo.CRule.bv_mult_pow2_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 [] => some Eo.CRule.bv_mult_pow2_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b [] => some Eo.CRule.bv_mult_pow2_2b
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit [] => some Eo.CRule.bv_extract_mult_leading_bit
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone [] => some Eo.CRule.bv_udiv_pow2_not_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero [] => some Eo.CRule.bv_udiv_zero
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone [] => some Eo.CRule.bv_udiv_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone [] => some Eo.CRule.bv_urem_pow2_not_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone [] => some Eo.CRule.bv_urem_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself [] => some Eo.CRule.bv_urem_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero [] => some Eo.CRule.bv_shl_zero
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero [] => some Eo.CRule.bv_lshr_zero
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero [] => some Eo.CRule.bv_ashr_zero
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem [] => some Eo.CRule.bv_ugt_urem
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone [] => some Eo.CRule.bv_ult_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 [] => some Eo.CRule.bv_merge_sign_extend_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 [] => some Eo.CRule.bv_merge_sign_extend_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 [] => some Eo.CRule.bv_sign_extend_eq_const_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 [] => some Eo.CRule.bv_sign_extend_eq_const_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 [] => some Eo.CRule.bv_zero_extend_eq_const_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 [] => some Eo.CRule.bv_zero_extend_eq_const_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 [] => some Eo.CRule.bv_zero_extend_ult_const_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 [] => some Eo.CRule.bv_zero_extend_ult_const_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 [] => some Eo.CRule.bv_sign_extend_ult_const_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 [] => some Eo.CRule.bv_sign_extend_ult_const_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 [] => some Eo.CRule.bv_sign_extend_ult_const_3
  | Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 [] => some Eo.CRule.bv_sign_extend_ult_const_4
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp [] => some Eo.CRule.sets_eq_singleton_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton [] => some Eo.CRule.sets_member_singleton
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp [] => some Eo.CRule.sets_member_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim [] => some Eo.CRule.sets_subset_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim [] => some Eo.CRule.sets_insert_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm [] => some Eo.CRule.sets_union_comm
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm [] => some Eo.CRule.sets_inter_comm
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 [] => some Eo.CRule.sets_inter_emp1
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 [] => some Eo.CRule.sets_inter_emp2
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 [] => some Eo.CRule.sets_minus_emp1
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 [] => some Eo.CRule.sets_minus_emp2
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 [] => some Eo.CRule.sets_union_emp1
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 [] => some Eo.CRule.sets_union_emp2
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember [] => some Eo.CRule.sets_inter_member
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember [] => some Eo.CRule.sets_minus_member
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember [] => some Eo.CRule.sets_union_member
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton [] => some Eo.CRule.sets_choose_singleton
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself [] => some Eo.CRule.sets_minus_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself [] => some Eo.CRule.sets_union_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself [] => some Eo.CRule.sets_inter_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim [] => some Eo.CRule.sets_is_empty_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim [] => some Eo.CRule.sets_is_singleton_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse [] => some Eo.CRule.str_eq_ctn_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 [] => some Eo.CRule.str_eq_ctn_full_false1
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 [] => some Eo.CRule.str_eq_ctn_full_false2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse [] => some Eo.CRule.str_eq_len_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr [] => some Eo.CRule.str_substr_empty_str
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange [] => some Eo.CRule.str_substr_empty_range
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart [] => some Eo.CRule.str_substr_empty_start
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg [] => some Eo.CRule.str_substr_empty_start_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen [] => some Eo.CRule.str_substr_substr_start_geq_len
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty [] => some Eo.CRule.str_substr_eq_empty
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq [] => some Eo.CRule.str_substr_z_eq_empty_leq
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen [] => some Eo.CRule.str_substr_eq_empty_leq_len
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv [] => some Eo.CRule.str_len_replace_inv
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv [] => some Eo.CRule.str_len_replace_all_inv
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv [] => some Eo.CRule.str_len_update_inv
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob [] => some Eo.CRule.str_update_oob
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev [] => some Eo.CRule.str_update_rev
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit [] => some Eo.CRule.str_update_fit
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 [] => some Eo.CRule.str_update_concat_fit0
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit [] => some Eo.CRule.str_update_concat_fit
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat [] => some Eo.CRule.str_update_in_first_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange [] => some Eo.CRule.str_len_substr_in_range
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash [] => some Eo.CRule.str_concat_clash
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev [] => some Eo.CRule.str_concat_clash_rev
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 [] => some Eo.CRule.str_concat_clash2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev [] => some Eo.CRule.str_concat_clash2_rev
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify [] => some Eo.CRule.str_concat_unify
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev [] => some Eo.CRule.str_concat_unify_rev
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase [] => some Eo.CRule.str_concat_unify_base
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev [] => some Eo.CRule.str_concat_unify_base_rev
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim [] => some Eo.CRule.str_prefixof_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim [] => some Eo.CRule.str_suffixof_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq [] => some Eo.CRule.str_prefixof_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq [] => some Eo.CRule.str_suffixof_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone [] => some Eo.CRule.str_prefixof_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone [] => some Eo.CRule.str_suffixof_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 [] => some Eo.CRule.str_substr_combine1
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 [] => some Eo.CRule.str_substr_combine2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 [] => some Eo.CRule.str_substr_combine3
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 [] => some Eo.CRule.str_substr_combine4
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 [] => some Eo.CRule.str_substr_concat1
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 [] => some Eo.CRule.str_substr_concat2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace [] => some Eo.CRule.str_substr_replace
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull [] => some Eo.CRule.str_substr_full
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq [] => some Eo.CRule.str_substr_full_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl [] => some Eo.CRule.str_contains_refl
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind [] => some Eo.CRule.str_contains_concat_find
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra [] => some Eo.CRule.str_contains_concat_find_contra
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar [] => some Eo.CRule.str_contains_split_char
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq [] => some Eo.CRule.str_contains_leq_len_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp [] => some Eo.CRule.str_contains_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar [] => some Eo.CRule.str_contains_char
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim [] => some Eo.CRule.str_at_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself [] => some Eo.CRule.str_replace_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid [] => some Eo.CRule.str_replace_id
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix [] => some Eo.CRule.str_replace_prefix
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat [] => some Eo.CRule.str_replace_prefix_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains [] => some Eo.CRule.str_replace_no_contains
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase [] => some Eo.CRule.str_replace_find_base
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat [] => some Eo.CRule.str_replace_find_first_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty [] => some Eo.CRule.str_replace_empty
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre [] => some Eo.CRule.str_replace_one_pre
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre [] => some Eo.CRule.str_replace_find_pre
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains [] => some Eo.CRule.str_replace_all_no_contains
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre [] => some Eo.CRule.str_replace_all_find_pre
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind [] => some Eo.CRule.str_replace_all_find
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty [] => some Eo.CRule.str_replace_all_empty
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid [] => some Eo.CRule.str_replace_all_id
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself [] => some Eo.CRule.str_replace_all_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone [] => some Eo.CRule.str_replace_re_none
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone [] => some Eo.CRule.str_replace_re_all_none
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec [] => some Eo.CRule.str_len_concat_rec
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec [] => some Eo.CRule.str_len_eq_zero_concat_rec
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase [] => some Eo.CRule.str_len_eq_zero_base
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself [] => some Eo.CRule.str_indexof_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains [] => some Eo.CRule.str_indexof_no_contains
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob [] => some Eo.CRule.str_indexof_oob
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 [] => some Eo.CRule.str_indexof_oob2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre [] => some Eo.CRule.str_indexof_contains_pre
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre [] => some Eo.CRule.str_indexof_contains_concat_pre
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat [] => some Eo.CRule.str_indexof_prefix_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob [] => some Eo.CRule.str_indexof_len_oob
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 [] => some Eo.CRule.str_indexof_len_oob2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp [] => some Eo.CRule.str_indexof_find_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr [] => some Eo.CRule.str_indexof_eq_irr
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone [] => some Eo.CRule.str_indexof_re_none
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre [] => some Eo.CRule.str_indexof_re_emp_re
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat [] => some Eo.CRule.str_to_lower_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat [] => some Eo.CRule.str_to_upper_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper [] => some Eo.CRule.str_to_lower_upper
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem [] => some Eo.CRule.str_to_lower_idem
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower [] => some Eo.CRule.str_to_upper_lower
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem [] => some Eo.CRule.str_to_upper_idem
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen [] => some Eo.CRule.str_to_lower_len
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen [] => some Eo.CRule.str_to_upper_len
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint [] => some Eo.CRule.str_to_lower_from_int
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint [] => some Eo.CRule.str_to_upper_from_int
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone [] => some Eo.CRule.str_to_int_concat_neg_one
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim [] => some Eo.CRule.str_is_digit_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty [] => some Eo.CRule.str_leq_empty
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq [] => some Eo.CRule.str_leq_empty_eq
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse [] => some Eo.CRule.str_leq_concat_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue [] => some Eo.CRule.str_leq_concat_true
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 [] => some Eo.CRule.str_leq_concat_base_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 [] => some Eo.CRule.str_leq_concat_base_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim [] => some Eo.CRule.str_lt_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit [] => some Eo.CRule.str_from_int_no_ctn_nondigit
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra [] => some Eo.CRule.str_substr_ctn_contra
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn [] => some Eo.CRule.str_substr_ctn
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn [] => some Eo.CRule.str_replace_dual_ctn
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse [] => some Eo.CRule.str_replace_dual_ctn_false
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp [] => some Eo.CRule.str_replace_self_ctn_simp
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc [] => some Eo.CRule.str_replace_emp_ctn_src
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen [] => some Eo.CRule.str_substr_char_start_eq_len
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar [] => some Eo.CRule.str_contains_repl_char
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar [] => some Eo.CRule.str_contains_repl_self_tgt_char
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself [] => some Eo.CRule.str_contains_repl_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt [] => some Eo.CRule.str_contains_repl_tgt
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid [] => some Eo.CRule.str_repl_repl_len_id
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn [] => some Eo.CRule.str_repl_repl_src_tgt_no_ctn
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself [] => some Eo.CRule.str_repl_repl_tgt_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn [] => some Eo.CRule.str_repl_repl_tgt_no_ctn
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself [] => some Eo.CRule.str_repl_repl_src_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 [] => some Eo.CRule.str_repl_repl_src_inv_no_ctn1
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 [] => some Eo.CRule.str_repl_repl_src_inv_no_ctn2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 [] => some Eo.CRule.str_repl_repl_src_inv_no_ctn3
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself [] => some Eo.CRule.str_repl_repl_dual_self
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 [] => some Eo.CRule.str_repl_repl_dual_ite1
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 [] => some Eo.CRule.str_repl_repl_dual_ite2
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp [] => some Eo.CRule.str_repl_repl_lookahead_id_simp
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim [] => some Eo.CRule.re_all_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim [] => some Eo.CRule.re_opt_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim [] => some Eo.CRule.re_diff_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim [] => some Eo.CRule.re_plus_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim [] => some Eo.CRule.re_repeat_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap [] => some Eo.CRule.re_concat_star_swap
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat [] => some Eo.CRule.re_concat_star_repeat
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 [] => some Eo.CRule.re_concat_star_nullable1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 [] => some Eo.CRule.re_concat_star_nullable2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge [] => some Eo.CRule.re_concat_merge
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall [] => some Eo.CRule.re_union_all
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim [] => some Eo.CRule.re_union_const_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall [] => some Eo.CRule.re_inter_all
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone [] => some Eo.CRule.re_star_none
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp [] => some Eo.CRule.re_star_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar [] => some Eo.CRule.re_star_star
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl [] => some Eo.CRule.re_range_refl
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp [] => some Eo.CRule.re_range_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 [] => some Eo.CRule.re_range_non_singleton_1
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 [] => some Eo.CRule.re_range_non_singleton_2
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar [] => some Eo.CRule.re_star_union_char
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp [] => some Eo.CRule.re_star_union_drop_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg [] => some Eo.CRule.re_loop_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar [] => some Eo.CRule.re_loop_star
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring [] => some Eo.CRule.re_inter_cstring
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg [] => some Eo.CRule.re_inter_cstring_neg
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude [] => some Eo.CRule.str_substr_len_include
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre [] => some Eo.CRule.str_substr_len_include_pre
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm [] => some Eo.CRule.str_substr_len_norm
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev [] => some Eo.CRule.seq_len_rev
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev [] => some Eo.CRule.seq_rev_rev
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat [] => some Eo.CRule.seq_rev_concat
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp [] => some Eo.CRule.str_eq_repl_self_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange [] => some Eo.CRule.str_eq_repl_no_change
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen [] => some Eo.CRule.str_eq_repl_tgt_eq_len
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix [] => some Eo.CRule.str_eq_repl_len_one_emp_prefix
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp [] => some Eo.CRule.str_eq_repl_emp_tgt_nemp
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp [] => some Eo.CRule.str_eq_repl_nemp_src_emp
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc [] => some Eo.CRule.str_eq_repl_self_src
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit [] => some Eo.CRule.seq_len_unit
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit [] => some Eo.CRule.seq_nth_unit
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit [] => some Eo.CRule.seq_nth_concat_unit
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen [] => some Eo.CRule.seq_nth_concat_unit_gen
  | Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit [] => some Eo.CRule.seq_rev_unit
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty [] => some Eo.CRule.re_in_empty
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma [] => some Eo.CRule.re_in_sigma
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar [] => some Eo.CRule.re_in_sigma_star
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring [] => some Eo.CRule.re_in_cstring
  | Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp [] => some Eo.CRule.re_in_comp
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim [] => some Eo.CRule.str_in_re_union_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim [] => some Eo.CRule.str_in_re_inter_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim [] => some Eo.CRule.str_in_re_range_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains [] => some Eo.CRule.str_in_re_contains
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange [] => some Eo.CRule.str_in_re_from_int_nemp_dig_range
  | Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange [] => some Eo.CRule.str_in_re_from_int_dig_range
  | Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5frefl [] => some Eo.CRule.eq_refl
  | Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fsymm [] => some Eo.CRule.eq_symm
  | Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq [] => some Eo.CRule.eq_cond_deq
  | Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift [] => some Eo.CRule.eq_ite_lift
  | Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim [] => some Eo.CRule.distinct_binary_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv [] => some Eo.CRule.uf_bv2nat_int2bv
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend [] => some Eo.CRule.uf_bv2nat_int2bv_extend
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract [] => some Eo.CRule.uf_bv2nat_int2bv_extract
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat [] => some Eo.CRule.uf_int2bv_bv2nat
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim [] => some Eo.CRule.uf_bv2nat_geq_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv [] => some Eo.CRule.uf_int2bv_bvult_equiv
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv [] => some Eo.CRule.uf_int2bv_bvule_equiv
  | Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim [] => some Eo.CRule.uf_sbv_to_int_elim
  | Tree.node schema.Constructor.eo__24emb_5fr_2eevaluate [] => some Eo.CRule.evaluate
  | Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues [] => some Eo.CRule.distinct_values
  | Tree.node schema.Constructor.eo__24emb_5fr_2eaci_5fnorm [] => some Eo.CRule.aci_norm
  | Tree.node schema.Constructor.eo__24emb_5fr_2eabsorb [] => some Eo.CRule.absorb
  | Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict [] => some Eo.CRule.distinct_card_conflict
  | _ => none
end

mutual
/-- A `CRule` that the store can hold: its natives fit the runtime's. -/
def emb_CRule : Eo.CRule → Prop
  | Eo.CRule.scope => True
  | Eo.CRule.process_scope => True
  | Eo.CRule.ite_eq => True
  | Eo.CRule.split => True
  | Eo.CRule.resolution => True
  | Eo.CRule.chain_resolution => True
  | Eo.CRule.chain_m_resolution => True
  | Eo.CRule.factoring => True
  | Eo.CRule.reordering => True
  | Eo.CRule.eq_resolve => True
  | Eo.CRule.modus_ponens => True
  | Eo.CRule.not_not_elim => True
  | Eo.CRule.contra => True
  | Eo.CRule.and_elim => True
  | Eo.CRule.and_intro => True
  | Eo.CRule.not_or_elim => True
  | Eo.CRule.implies_elim => True
  | Eo.CRule.not_implies_elim1 => True
  | Eo.CRule.not_implies_elim2 => True
  | Eo.CRule.equiv_elim1 => True
  | Eo.CRule.equiv_elim2 => True
  | Eo.CRule.not_equiv_elim1 => True
  | Eo.CRule.not_equiv_elim2 => True
  | Eo.CRule.xor_elim1 => True
  | Eo.CRule.xor_elim2 => True
  | Eo.CRule.not_xor_elim1 => True
  | Eo.CRule.not_xor_elim2 => True
  | Eo.CRule.ite_elim1 => True
  | Eo.CRule.ite_elim2 => True
  | Eo.CRule.not_ite_elim1 => True
  | Eo.CRule.not_ite_elim2 => True
  | Eo.CRule.not_and => True
  | Eo.CRule.cnf_and_pos => True
  | Eo.CRule.cnf_and_neg => True
  | Eo.CRule.cnf_or_pos => True
  | Eo.CRule.cnf_or_neg => True
  | Eo.CRule.cnf_implies_pos => True
  | Eo.CRule.cnf_implies_neg1 => True
  | Eo.CRule.cnf_implies_neg2 => True
  | Eo.CRule.cnf_equiv_pos1 => True
  | Eo.CRule.cnf_equiv_pos2 => True
  | Eo.CRule.cnf_equiv_neg1 => True
  | Eo.CRule.cnf_equiv_neg2 => True
  | Eo.CRule.cnf_xor_pos1 => True
  | Eo.CRule.cnf_xor_pos2 => True
  | Eo.CRule.cnf_xor_neg1 => True
  | Eo.CRule.cnf_xor_neg2 => True
  | Eo.CRule.cnf_ite_pos1 => True
  | Eo.CRule.cnf_ite_pos2 => True
  | Eo.CRule.cnf_ite_pos3 => True
  | Eo.CRule.cnf_ite_neg1 => True
  | Eo.CRule.cnf_ite_neg2 => True
  | Eo.CRule.cnf_ite_neg3 => True
  | Eo.CRule.arrays_read_over_write => True
  | Eo.CRule.arrays_read_over_write_contra => True
  | Eo.CRule.arrays_read_over_write_1 => True
  | Eo.CRule.arrays_ext => True
  | Eo.CRule.refl => True
  | Eo.CRule.symm => True
  | Eo.CRule.trans => True
  | Eo.CRule.cong => True
  | Eo.CRule.nary_cong => True
  | Eo.CRule.pairwise_cong => True
  | Eo.CRule.true_intro => True
  | Eo.CRule.true_elim => True
  | Eo.CRule.false_intro => True
  | Eo.CRule.false_elim => True
  | Eo.CRule.ho_cong => True
  | Eo.CRule.distinct_elim => True
  | Eo.CRule.distinct_true => True
  | Eo.CRule.distinct_false => True
  | Eo.CRule.arith_sum_ub => True
  | Eo.CRule.arith_mult_pos => True
  | Eo.CRule.arith_mult_neg => True
  | Eo.CRule.arith_trichotomy => True
  | Eo.CRule.int_tight_ub => True
  | Eo.CRule.int_tight_lb => True
  | Eo.CRule.arith_mult_tangent => True
  | Eo.CRule.arith_mult_sign => True
  | Eo.CRule.arith_mult_abs_comparison => True
  | Eo.CRule.arith_reduction => True
  | Eo.CRule.arith_poly_norm => True
  | Eo.CRule.arith_poly_norm_rel => True
  | Eo.CRule.bv_repeat_elim => True
  | Eo.CRule.bv_smulo_elim => True
  | Eo.CRule.bv_umulo_elim => True
  | Eo.CRule.bv_bitwise_slicing => True
  | Eo.CRule.bv_bitblast_step => True
  | Eo.CRule.bv_poly_norm => True
  | Eo.CRule.bv_poly_norm_eq => True
  | Eo.CRule.string_length_pos => True
  | Eo.CRule.string_length_non_empty => True
  | Eo.CRule.concat_eq => True
  | Eo.CRule.concat_unify => True
  | Eo.CRule.concat_csplit => True
  | Eo.CRule.concat_split => True
  | Eo.CRule.concat_lprop => True
  | Eo.CRule.concat_cprop => True
  | Eo.CRule.string_decompose => True
  | Eo.CRule.exists_string_length => True
  | Eo.CRule.string_code_inj => True
  | Eo.CRule.string_seq_unit_inj => True
  | Eo.CRule.re_inter => True
  | Eo.CRule.re_concat => True
  | Eo.CRule.re_unfold_pos => True
  | Eo.CRule.re_unfold_neg_concat_fixed => True
  | Eo.CRule.re_unfold_neg => True
  | Eo.CRule.string_ext => True
  | Eo.CRule.string_reduction => True
  | Eo.CRule.string_eager_reduction => True
  | Eo.CRule.arith_string_pred_entail => True
  | Eo.CRule.arith_string_pred_safe_approx => True
  | Eo.CRule.str_in_re_eval => True
  | Eo.CRule.str_in_re_consume => True
  | Eo.CRule.re_loop_elim => True
  | Eo.CRule.re_eq_elim => True
  | Eo.CRule.re_inter_inclusion => True
  | Eo.CRule.re_union_inclusion => True
  | Eo.CRule.str_in_re_concat_star_char => True
  | Eo.CRule.str_in_re_sigma => True
  | Eo.CRule.str_in_re_sigma_star => True
  | Eo.CRule.str_ctn_multiset_subset => True
  | Eo.CRule.str_overlap_split_ctn => True
  | Eo.CRule.str_overlap_endpoints_ctn => True
  | Eo.CRule.str_overlap_endpoints_indexof => True
  | Eo.CRule.str_overlap_endpoints_replace => True
  | Eo.CRule.str_indexof_re_eval => True
  | Eo.CRule.str_replace_re_eval => True
  | Eo.CRule.str_replace_re_all_eval => True
  | Eo.CRule.seq_eval_op => True
  | Eo.CRule.sets_singleton_inj => True
  | Eo.CRule.sets_ext => True
  | Eo.CRule.sets_choose_member => True
  | Eo.CRule.sets_eval_op => True
  | Eo.CRule.ubv_to_int_range => True
  | Eo.CRule.ubv_to_int_elim => True
  | Eo.CRule.int_to_bv_elim => True
  | Eo.CRule.instantiate => True
  | Eo.CRule.skolemize => True
  | Eo.CRule.skolem_intro => True
  | Eo.CRule.alpha_equiv => True
  | Eo.CRule.beta_reduce => True
  | Eo.CRule.quant_var_reordering => True
  | Eo.CRule.exists_elim => True
  | Eo.CRule.quant_unused_vars => True
  | Eo.CRule.quant_merge_prenex => True
  | Eo.CRule.quant_miniscope_and => True
  | Eo.CRule.quant_miniscope_or => True
  | Eo.CRule.quant_miniscope_ite => True
  | Eo.CRule.quant_var_elim_eq => True
  | Eo.CRule.quant_dt_split => True
  | Eo.CRule.dt_split => True
  | Eo.CRule.dt_inst => True
  | Eo.CRule.dt_collapse_selector => True
  | Eo.CRule.dt_collapse_tester => True
  | Eo.CRule.dt_collapse_tester_singleton => True
  | Eo.CRule.dt_cons_eq => True
  | Eo.CRule.dt_cons_eq_clash => True
  | Eo.CRule.dt_cycle => True
  | Eo.CRule.dt_collapse_updater => True
  | Eo.CRule.dt_updater_elim => True
  | Eo.CRule.arith_div_total_zero_real => True
  | Eo.CRule.arith_div_total_zero_int => True
  | Eo.CRule.arith_int_div_total => True
  | Eo.CRule.arith_int_div_total_one => True
  | Eo.CRule.arith_int_div_total_zero => True
  | Eo.CRule.arith_int_div_total_neg => True
  | Eo.CRule.arith_int_mod_total => True
  | Eo.CRule.arith_int_mod_total_one => True
  | Eo.CRule.arith_int_mod_total_zero => True
  | Eo.CRule.arith_int_mod_total_neg => True
  | Eo.CRule.arith_int_div_total_over_mod => True
  | Eo.CRule.arith_elim_gt => True
  | Eo.CRule.arith_elim_lt => True
  | Eo.CRule.arith_elim_int_gt => True
  | Eo.CRule.arith_elim_int_lt => True
  | Eo.CRule.arith_elim_leq => True
  | Eo.CRule.arith_leq_norm => True
  | Eo.CRule.arith_geq_tighten => True
  | Eo.CRule.arith_geq_norm1_int => True
  | Eo.CRule.arith_geq_norm1_real => True
  | Eo.CRule.arith_eq_elim_real => True
  | Eo.CRule.arith_eq_elim_int => True
  | Eo.CRule.arith_to_int_elim_to_real => True
  | Eo.CRule.arith_is_int_elim_to_real => True
  | Eo.CRule.arith_div_int_to_real => True
  | Eo.CRule.arith_div_total_int_to_real => True
  | Eo.CRule.arith_mod_over_mod_1 => True
  | Eo.CRule.arith_mod_over_mod => True
  | Eo.CRule.arith_mod_over_mod_mult => True
  | Eo.CRule.arith_int_eq_conflict => True
  | Eo.CRule.arith_int_geq_tighten => True
  | Eo.CRule.arith_divisible_elim => True
  | Eo.CRule.arith_abs_eq => True
  | Eo.CRule.arith_abs_int_gt => True
  | Eo.CRule.arith_abs_real_gt => True
  | Eo.CRule.arith_geq_ite_lift => True
  | Eo.CRule.arith_leq_ite_lift => True
  | Eo.CRule.arith_min_lt1 => True
  | Eo.CRule.arith_min_lt2 => True
  | Eo.CRule.arith_max_geq1 => True
  | Eo.CRule.arith_max_geq2 => True
  | Eo.CRule.array_read_over_write => True
  | Eo.CRule.array_read_over_write2 => True
  | Eo.CRule.array_store_overwrite => True
  | Eo.CRule.array_store_self => True
  | Eo.CRule.array_read_over_write_split => True
  | Eo.CRule.array_store_swap => True
  | Eo.CRule.bool_double_not_elim => True
  | Eo.CRule.bool_not_true => True
  | Eo.CRule.bool_not_false => True
  | Eo.CRule.bool_eq_true => True
  | Eo.CRule.bool_eq_false => True
  | Eo.CRule.bool_eq_nrefl => True
  | Eo.CRule.bool_impl_false1 => True
  | Eo.CRule.bool_impl_false2 => True
  | Eo.CRule.bool_impl_true1 => True
  | Eo.CRule.bool_impl_true2 => True
  | Eo.CRule.bool_impl_elim => True
  | Eo.CRule.bool_dual_impl_eq => True
  | Eo.CRule.bool_and_conf => True
  | Eo.CRule.bool_and_conf2 => True
  | Eo.CRule.bool_or_taut => True
  | Eo.CRule.bool_or_taut2 => True
  | Eo.CRule.bool_or_de_morgan => True
  | Eo.CRule.bool_implies_de_morgan => True
  | Eo.CRule.bool_and_de_morgan => True
  | Eo.CRule.bool_or_and_distrib => True
  | Eo.CRule.bool_implies_or_distrib => True
  | Eo.CRule.bool_xor_refl => True
  | Eo.CRule.bool_xor_nrefl => True
  | Eo.CRule.bool_xor_false => True
  | Eo.CRule.bool_xor_true => True
  | Eo.CRule.bool_xor_comm => True
  | Eo.CRule.bool_xor_elim => True
  | Eo.CRule.bool_not_xor_elim => True
  | Eo.CRule.bool_not_eq_elim1 => True
  | Eo.CRule.bool_not_eq_elim2 => True
  | Eo.CRule.ite_neg_branch => True
  | Eo.CRule.ite_then_true => True
  | Eo.CRule.ite_else_false => True
  | Eo.CRule.ite_then_false => True
  | Eo.CRule.ite_else_true => True
  | Eo.CRule.ite_then_lookahead_self => True
  | Eo.CRule.ite_else_lookahead_self => True
  | Eo.CRule.ite_then_lookahead_not_self => True
  | Eo.CRule.ite_else_lookahead_not_self => True
  | Eo.CRule.ite_expand => True
  | Eo.CRule.bool_not_ite_elim => True
  | Eo.CRule.ite_true_cond => True
  | Eo.CRule.ite_false_cond => True
  | Eo.CRule.ite_not_cond => True
  | Eo.CRule.ite_eq_branch => True
  | Eo.CRule.ite_then_lookahead => True
  | Eo.CRule.ite_else_lookahead => True
  | Eo.CRule.ite_then_neg_lookahead => True
  | Eo.CRule.ite_else_neg_lookahead => True
  | Eo.CRule.bv_concat_extract_merge => True
  | Eo.CRule.bv_extract_extract => True
  | Eo.CRule.bv_extract_whole => True
  | Eo.CRule.bv_extract_concat_1 => True
  | Eo.CRule.bv_extract_concat_2 => True
  | Eo.CRule.bv_extract_concat_3 => True
  | Eo.CRule.bv_extract_concat_4 => True
  | Eo.CRule.bv_eq_extract_elim1 => True
  | Eo.CRule.bv_eq_extract_elim2 => True
  | Eo.CRule.bv_eq_extract_elim3 => True
  | Eo.CRule.bv_extract_not => True
  | Eo.CRule.bv_extract_sign_extend_1 => True
  | Eo.CRule.bv_extract_sign_extend_2 => True
  | Eo.CRule.bv_extract_sign_extend_3 => True
  | Eo.CRule.bv_not_xor => True
  | Eo.CRule.bv_and_simplify_1 => True
  | Eo.CRule.bv_and_simplify_2 => True
  | Eo.CRule.bv_or_simplify_1 => True
  | Eo.CRule.bv_or_simplify_2 => True
  | Eo.CRule.bv_xor_simplify_1 => True
  | Eo.CRule.bv_xor_simplify_2 => True
  | Eo.CRule.bv_xor_simplify_3 => True
  | Eo.CRule.bv_ult_add_one => True
  | Eo.CRule.bv_mult_slt_mult_1 => True
  | Eo.CRule.bv_mult_slt_mult_2 => True
  | Eo.CRule.bv_commutative_xor => True
  | Eo.CRule.bv_commutative_comp => True
  | Eo.CRule.bv_zero_extend_eliminate_0 => True
  | Eo.CRule.bv_sign_extend_eliminate_0 => True
  | Eo.CRule.bv_not_neq => True
  | Eo.CRule.bv_ult_ones => True
  | Eo.CRule.bv_concat_merge_const => True
  | Eo.CRule.bv_commutative_add => True
  | Eo.CRule.bv_sub_eliminate => True
  | Eo.CRule.bv_ite_width_one => True
  | Eo.CRule.bv_ite_width_one_not => True
  | Eo.CRule.bv_eq_xor_solve => True
  | Eo.CRule.bv_eq_not_solve => True
  | Eo.CRule.bv_ugt_eliminate => True
  | Eo.CRule.bv_uge_eliminate => True
  | Eo.CRule.bv_sgt_eliminate => True
  | Eo.CRule.bv_sge_eliminate => True
  | Eo.CRule.bv_sle_eliminate => True
  | Eo.CRule.bv_redor_eliminate => True
  | Eo.CRule.bv_redand_eliminate => True
  | Eo.CRule.bv_ule_eliminate => True
  | Eo.CRule.bv_comp_eliminate => True
  | Eo.CRule.bv_rotate_left_eliminate_1 => True
  | Eo.CRule.bv_rotate_left_eliminate_2 => True
  | Eo.CRule.bv_rotate_right_eliminate_1 => True
  | Eo.CRule.bv_rotate_right_eliminate_2 => True
  | Eo.CRule.bv_nand_eliminate => True
  | Eo.CRule.bv_nor_eliminate => True
  | Eo.CRule.bv_xnor_eliminate => True
  | Eo.CRule.bv_sdiv_eliminate => True
  | Eo.CRule.bv_zero_extend_eliminate => True
  | Eo.CRule.bv_uaddo_eliminate => True
  | Eo.CRule.bv_saddo_eliminate => True
  | Eo.CRule.bv_sdivo_eliminate => True
  | Eo.CRule.bv_smod_eliminate => True
  | Eo.CRule.bv_srem_eliminate => True
  | Eo.CRule.bv_usubo_eliminate => True
  | Eo.CRule.bv_ssubo_eliminate => True
  | Eo.CRule.bv_nego_eliminate => True
  | Eo.CRule.bv_ite_equal_children => True
  | Eo.CRule.bv_ite_const_cond_1 => True
  | Eo.CRule.bv_ite_const_cond_2 => True
  | Eo.CRule.bv_ite_const_children_1 => True
  | Eo.CRule.bv_ite_const_children_2 => True
  | Eo.CRule.bv_ite_equal_cond_1 => True
  | Eo.CRule.bv_ite_equal_cond_2 => True
  | Eo.CRule.bv_ite_equal_cond_3 => True
  | Eo.CRule.bv_ite_merge_then_if => True
  | Eo.CRule.bv_ite_merge_else_if => True
  | Eo.CRule.bv_ite_merge_then_else => True
  | Eo.CRule.bv_ite_merge_else_else => True
  | Eo.CRule.bv_shl_by_const_0 => True
  | Eo.CRule.bv_shl_by_const_1 => True
  | Eo.CRule.bv_shl_by_const_2 => True
  | Eo.CRule.bv_lshr_by_const_0 => True
  | Eo.CRule.bv_lshr_by_const_1 => True
  | Eo.CRule.bv_lshr_by_const_2 => True
  | Eo.CRule.bv_ashr_by_const_0 => True
  | Eo.CRule.bv_ashr_by_const_1 => True
  | Eo.CRule.bv_ashr_by_const_2 => True
  | Eo.CRule.bv_and_concat_pullup => True
  | Eo.CRule.bv_or_concat_pullup => True
  | Eo.CRule.bv_xor_concat_pullup => True
  | Eo.CRule.bv_and_concat_pullup2 => True
  | Eo.CRule.bv_or_concat_pullup2 => True
  | Eo.CRule.bv_xor_concat_pullup2 => True
  | Eo.CRule.bv_and_concat_pullup3 => True
  | Eo.CRule.bv_or_concat_pullup3 => True
  | Eo.CRule.bv_xor_concat_pullup3 => True
  | Eo.CRule.bv_xor_duplicate => True
  | Eo.CRule.bv_xor_ones => True
  | Eo.CRule.bv_xor_not => True
  | Eo.CRule.bv_not_idemp => True
  | Eo.CRule.bv_ult_zero_1 => True
  | Eo.CRule.bv_ult_zero_2 => True
  | Eo.CRule.bv_ult_self => True
  | Eo.CRule.bv_lt_self => True
  | Eo.CRule.bv_ule_self => True
  | Eo.CRule.bv_ule_zero => True
  | Eo.CRule.bv_zero_ule => True
  | Eo.CRule.bv_sle_self => True
  | Eo.CRule.bv_ule_max => True
  | Eo.CRule.bv_not_ult => True
  | Eo.CRule.bv_mult_pow2_1 => True
  | Eo.CRule.bv_mult_pow2_2 => True
  | Eo.CRule.bv_mult_pow2_2b => True
  | Eo.CRule.bv_extract_mult_leading_bit => True
  | Eo.CRule.bv_udiv_pow2_not_one => True
  | Eo.CRule.bv_udiv_zero => True
  | Eo.CRule.bv_udiv_one => True
  | Eo.CRule.bv_urem_pow2_not_one => True
  | Eo.CRule.bv_urem_one => True
  | Eo.CRule.bv_urem_self => True
  | Eo.CRule.bv_shl_zero => True
  | Eo.CRule.bv_lshr_zero => True
  | Eo.CRule.bv_ashr_zero => True
  | Eo.CRule.bv_ugt_urem => True
  | Eo.CRule.bv_ult_one => True
  | Eo.CRule.bv_merge_sign_extend_1 => True
  | Eo.CRule.bv_merge_sign_extend_2 => True
  | Eo.CRule.bv_sign_extend_eq_const_1 => True
  | Eo.CRule.bv_sign_extend_eq_const_2 => True
  | Eo.CRule.bv_zero_extend_eq_const_1 => True
  | Eo.CRule.bv_zero_extend_eq_const_2 => True
  | Eo.CRule.bv_zero_extend_ult_const_1 => True
  | Eo.CRule.bv_zero_extend_ult_const_2 => True
  | Eo.CRule.bv_sign_extend_ult_const_1 => True
  | Eo.CRule.bv_sign_extend_ult_const_2 => True
  | Eo.CRule.bv_sign_extend_ult_const_3 => True
  | Eo.CRule.bv_sign_extend_ult_const_4 => True
  | Eo.CRule.sets_eq_singleton_emp => True
  | Eo.CRule.sets_member_singleton => True
  | Eo.CRule.sets_member_emp => True
  | Eo.CRule.sets_subset_elim => True
  | Eo.CRule.sets_insert_elim => True
  | Eo.CRule.sets_union_comm => True
  | Eo.CRule.sets_inter_comm => True
  | Eo.CRule.sets_inter_emp1 => True
  | Eo.CRule.sets_inter_emp2 => True
  | Eo.CRule.sets_minus_emp1 => True
  | Eo.CRule.sets_minus_emp2 => True
  | Eo.CRule.sets_union_emp1 => True
  | Eo.CRule.sets_union_emp2 => True
  | Eo.CRule.sets_inter_member => True
  | Eo.CRule.sets_minus_member => True
  | Eo.CRule.sets_union_member => True
  | Eo.CRule.sets_choose_singleton => True
  | Eo.CRule.sets_minus_self => True
  | Eo.CRule.sets_union_self => True
  | Eo.CRule.sets_inter_self => True
  | Eo.CRule.sets_is_empty_elim => True
  | Eo.CRule.sets_is_singleton_elim => True
  | Eo.CRule.str_eq_ctn_false => True
  | Eo.CRule.str_eq_ctn_full_false1 => True
  | Eo.CRule.str_eq_ctn_full_false2 => True
  | Eo.CRule.str_eq_len_false => True
  | Eo.CRule.str_substr_empty_str => True
  | Eo.CRule.str_substr_empty_range => True
  | Eo.CRule.str_substr_empty_start => True
  | Eo.CRule.str_substr_empty_start_neg => True
  | Eo.CRule.str_substr_substr_start_geq_len => True
  | Eo.CRule.str_substr_eq_empty => True
  | Eo.CRule.str_substr_z_eq_empty_leq => True
  | Eo.CRule.str_substr_eq_empty_leq_len => True
  | Eo.CRule.str_len_replace_inv => True
  | Eo.CRule.str_len_replace_all_inv => True
  | Eo.CRule.str_len_update_inv => True
  | Eo.CRule.str_update_oob => True
  | Eo.CRule.str_update_rev => True
  | Eo.CRule.str_update_fit => True
  | Eo.CRule.str_update_concat_fit0 => True
  | Eo.CRule.str_update_concat_fit => True
  | Eo.CRule.str_update_in_first_concat => True
  | Eo.CRule.str_len_substr_in_range => True
  | Eo.CRule.str_concat_clash => True
  | Eo.CRule.str_concat_clash_rev => True
  | Eo.CRule.str_concat_clash2 => True
  | Eo.CRule.str_concat_clash2_rev => True
  | Eo.CRule.str_concat_unify => True
  | Eo.CRule.str_concat_unify_rev => True
  | Eo.CRule.str_concat_unify_base => True
  | Eo.CRule.str_concat_unify_base_rev => True
  | Eo.CRule.str_prefixof_elim => True
  | Eo.CRule.str_suffixof_elim => True
  | Eo.CRule.str_prefixof_eq => True
  | Eo.CRule.str_suffixof_eq => True
  | Eo.CRule.str_prefixof_one => True
  | Eo.CRule.str_suffixof_one => True
  | Eo.CRule.str_substr_combine1 => True
  | Eo.CRule.str_substr_combine2 => True
  | Eo.CRule.str_substr_combine3 => True
  | Eo.CRule.str_substr_combine4 => True
  | Eo.CRule.str_substr_concat1 => True
  | Eo.CRule.str_substr_concat2 => True
  | Eo.CRule.str_substr_replace => True
  | Eo.CRule.str_substr_full => True
  | Eo.CRule.str_substr_full_eq => True
  | Eo.CRule.str_contains_refl => True
  | Eo.CRule.str_contains_concat_find => True
  | Eo.CRule.str_contains_concat_find_contra => True
  | Eo.CRule.str_contains_split_char => True
  | Eo.CRule.str_contains_leq_len_eq => True
  | Eo.CRule.str_contains_emp => True
  | Eo.CRule.str_contains_char => True
  | Eo.CRule.str_at_elim => True
  | Eo.CRule.str_replace_self => True
  | Eo.CRule.str_replace_id => True
  | Eo.CRule.str_replace_prefix => True
  | Eo.CRule.str_replace_prefix_concat => True
  | Eo.CRule.str_replace_no_contains => True
  | Eo.CRule.str_replace_find_base => True
  | Eo.CRule.str_replace_find_first_concat => True
  | Eo.CRule.str_replace_empty => True
  | Eo.CRule.str_replace_one_pre => True
  | Eo.CRule.str_replace_find_pre => True
  | Eo.CRule.str_replace_all_no_contains => True
  | Eo.CRule.str_replace_all_find_pre => True
  | Eo.CRule.str_replace_all_find => True
  | Eo.CRule.str_replace_all_empty => True
  | Eo.CRule.str_replace_all_id => True
  | Eo.CRule.str_replace_all_self => True
  | Eo.CRule.str_replace_re_none => True
  | Eo.CRule.str_replace_re_all_none => True
  | Eo.CRule.str_len_concat_rec => True
  | Eo.CRule.str_len_eq_zero_concat_rec => True
  | Eo.CRule.str_len_eq_zero_base => True
  | Eo.CRule.str_indexof_self => True
  | Eo.CRule.str_indexof_no_contains => True
  | Eo.CRule.str_indexof_oob => True
  | Eo.CRule.str_indexof_oob2 => True
  | Eo.CRule.str_indexof_contains_pre => True
  | Eo.CRule.str_indexof_contains_concat_pre => True
  | Eo.CRule.str_indexof_prefix_concat => True
  | Eo.CRule.str_indexof_len_oob => True
  | Eo.CRule.str_indexof_len_oob2 => True
  | Eo.CRule.str_indexof_find_emp => True
  | Eo.CRule.str_indexof_eq_irr => True
  | Eo.CRule.str_indexof_re_none => True
  | Eo.CRule.str_indexof_re_emp_re => True
  | Eo.CRule.str_to_lower_concat => True
  | Eo.CRule.str_to_upper_concat => True
  | Eo.CRule.str_to_lower_upper => True
  | Eo.CRule.str_to_lower_idem => True
  | Eo.CRule.str_to_upper_lower => True
  | Eo.CRule.str_to_upper_idem => True
  | Eo.CRule.str_to_lower_len => True
  | Eo.CRule.str_to_upper_len => True
  | Eo.CRule.str_to_lower_from_int => True
  | Eo.CRule.str_to_upper_from_int => True
  | Eo.CRule.str_to_int_concat_neg_one => True
  | Eo.CRule.str_is_digit_elim => True
  | Eo.CRule.str_leq_empty => True
  | Eo.CRule.str_leq_empty_eq => True
  | Eo.CRule.str_leq_concat_false => True
  | Eo.CRule.str_leq_concat_true => True
  | Eo.CRule.str_leq_concat_base_1 => True
  | Eo.CRule.str_leq_concat_base_2 => True
  | Eo.CRule.str_lt_elim => True
  | Eo.CRule.str_from_int_no_ctn_nondigit => True
  | Eo.CRule.str_substr_ctn_contra => True
  | Eo.CRule.str_substr_ctn => True
  | Eo.CRule.str_replace_dual_ctn => True
  | Eo.CRule.str_replace_dual_ctn_false => True
  | Eo.CRule.str_replace_self_ctn_simp => True
  | Eo.CRule.str_replace_emp_ctn_src => True
  | Eo.CRule.str_substr_char_start_eq_len => True
  | Eo.CRule.str_contains_repl_char => True
  | Eo.CRule.str_contains_repl_self_tgt_char => True
  | Eo.CRule.str_contains_repl_self => True
  | Eo.CRule.str_contains_repl_tgt => True
  | Eo.CRule.str_repl_repl_len_id => True
  | Eo.CRule.str_repl_repl_src_tgt_no_ctn => True
  | Eo.CRule.str_repl_repl_tgt_self => True
  | Eo.CRule.str_repl_repl_tgt_no_ctn => True
  | Eo.CRule.str_repl_repl_src_self => True
  | Eo.CRule.str_repl_repl_src_inv_no_ctn1 => True
  | Eo.CRule.str_repl_repl_src_inv_no_ctn2 => True
  | Eo.CRule.str_repl_repl_src_inv_no_ctn3 => True
  | Eo.CRule.str_repl_repl_dual_self => True
  | Eo.CRule.str_repl_repl_dual_ite1 => True
  | Eo.CRule.str_repl_repl_dual_ite2 => True
  | Eo.CRule.str_repl_repl_lookahead_id_simp => True
  | Eo.CRule.re_all_elim => True
  | Eo.CRule.re_opt_elim => True
  | Eo.CRule.re_diff_elim => True
  | Eo.CRule.re_plus_elim => True
  | Eo.CRule.re_repeat_elim => True
  | Eo.CRule.re_concat_star_swap => True
  | Eo.CRule.re_concat_star_repeat => True
  | Eo.CRule.re_concat_star_nullable1 => True
  | Eo.CRule.re_concat_star_nullable2 => True
  | Eo.CRule.re_concat_merge => True
  | Eo.CRule.re_union_all => True
  | Eo.CRule.re_union_const_elim => True
  | Eo.CRule.re_inter_all => True
  | Eo.CRule.re_star_none => True
  | Eo.CRule.re_star_emp => True
  | Eo.CRule.re_star_star => True
  | Eo.CRule.re_range_refl => True
  | Eo.CRule.re_range_emp => True
  | Eo.CRule.re_range_non_singleton_1 => True
  | Eo.CRule.re_range_non_singleton_2 => True
  | Eo.CRule.re_star_union_char => True
  | Eo.CRule.re_star_union_drop_emp => True
  | Eo.CRule.re_loop_neg => True
  | Eo.CRule.re_loop_star => True
  | Eo.CRule.re_inter_cstring => True
  | Eo.CRule.re_inter_cstring_neg => True
  | Eo.CRule.str_substr_len_include => True
  | Eo.CRule.str_substr_len_include_pre => True
  | Eo.CRule.str_substr_len_norm => True
  | Eo.CRule.seq_len_rev => True
  | Eo.CRule.seq_rev_rev => True
  | Eo.CRule.seq_rev_concat => True
  | Eo.CRule.str_eq_repl_self_emp => True
  | Eo.CRule.str_eq_repl_no_change => True
  | Eo.CRule.str_eq_repl_tgt_eq_len => True
  | Eo.CRule.str_eq_repl_len_one_emp_prefix => True
  | Eo.CRule.str_eq_repl_emp_tgt_nemp => True
  | Eo.CRule.str_eq_repl_nemp_src_emp => True
  | Eo.CRule.str_eq_repl_self_src => True
  | Eo.CRule.seq_len_unit => True
  | Eo.CRule.seq_nth_unit => True
  | Eo.CRule.seq_nth_concat_unit => True
  | Eo.CRule.seq_nth_concat_unit_gen => True
  | Eo.CRule.seq_rev_unit => True
  | Eo.CRule.re_in_empty => True
  | Eo.CRule.re_in_sigma => True
  | Eo.CRule.re_in_sigma_star => True
  | Eo.CRule.re_in_cstring => True
  | Eo.CRule.re_in_comp => True
  | Eo.CRule.str_in_re_union_elim => True
  | Eo.CRule.str_in_re_inter_elim => True
  | Eo.CRule.str_in_re_range_elim => True
  | Eo.CRule.str_in_re_contains => True
  | Eo.CRule.str_in_re_from_int_nemp_dig_range => True
  | Eo.CRule.str_in_re_from_int_dig_range => True
  | Eo.CRule.eq_refl => True
  | Eo.CRule.eq_symm => True
  | Eo.CRule.eq_cond_deq => True
  | Eo.CRule.eq_ite_lift => True
  | Eo.CRule.distinct_binary_elim => True
  | Eo.CRule.uf_bv2nat_int2bv => True
  | Eo.CRule.uf_bv2nat_int2bv_extend => True
  | Eo.CRule.uf_bv2nat_int2bv_extract => True
  | Eo.CRule.uf_int2bv_bv2nat => True
  | Eo.CRule.uf_bv2nat_geq_elim => True
  | Eo.CRule.uf_int2bv_bvult_equiv => True
  | Eo.CRule.uf_int2bv_bvule_equiv => True
  | Eo.CRule.uf_sbv_to_int_elim => True
  | Eo.CRule.evaluate => True
  | Eo.CRule.distinct_values => True
  | Eo.CRule.aci_norm => True
  | Eo.CRule.absorb => True
  | Eo.CRule.distinct_card_conflict => True
end

mutual
theorem dec_enc_CRule : (x : Eo.CRule) → emb_CRule x → dec_CRule (enc_CRule x) = some x
  | Eo.CRule.scope, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.process_scope, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.split, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.resolution, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.chain_resolution, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.chain_m_resolution, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.factoring, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.reordering, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.eq_resolve, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.modus_ponens, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_not_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.contra, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.and_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.and_intro, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_or_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.implies_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_implies_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_implies_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.equiv_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.equiv_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_equiv_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_equiv_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.xor_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.xor_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_xor_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_xor_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_ite_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_ite_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.not_and, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_and_pos, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_and_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_or_pos, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_or_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_implies_pos, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_implies_neg1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_implies_neg2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_equiv_pos1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_equiv_pos2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_equiv_neg1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_equiv_neg2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_xor_pos1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_xor_pos2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_xor_neg1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_xor_neg2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_ite_pos1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_ite_pos2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_ite_pos3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_ite_neg1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_ite_neg2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.cnf_ite_neg3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arrays_read_over_write, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arrays_read_over_write_contra, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arrays_read_over_write_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arrays_ext, h => by
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
  | Eo.CRule.cong, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.nary_cong, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.pairwise_cong, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.true_intro, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.true_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.false_intro, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.false_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ho_cong, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.distinct_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.distinct_true, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.distinct_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_sum_ub, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mult_pos, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mult_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_trichotomy, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.int_tight_ub, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.int_tight_lb, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mult_tangent, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mult_sign, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mult_abs_comparison, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_reduction, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_poly_norm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_poly_norm_rel, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_repeat_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_smulo_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_umulo_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_bitwise_slicing, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_bitblast_step, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_poly_norm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_poly_norm_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_length_pos, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_length_non_empty, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.concat_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.concat_unify, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.concat_csplit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.concat_split, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.concat_lprop, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.concat_cprop, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_decompose, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.exists_string_length, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_code_inj, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_seq_unit_inj, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_inter, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_unfold_pos, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_unfold_neg_concat_fixed, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_unfold_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_ext, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_reduction, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.string_eager_reduction, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_string_pred_entail, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_string_pred_safe_approx, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_eval, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_consume, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_loop_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_eq_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_inter_inclusion, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_union_inclusion, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_concat_star_char, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_sigma, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_sigma_star, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_ctn_multiset_subset, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_overlap_split_ctn, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_overlap_endpoints_ctn, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_overlap_endpoints_indexof, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_overlap_endpoints_replace, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_re_eval, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_re_eval, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_re_all_eval, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_eval_op, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_singleton_inj, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_ext, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_choose_member, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_eval_op, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ubv_to_int_range, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ubv_to_int_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.int_to_bv_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.instantiate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.skolemize, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.skolem_intro, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.alpha_equiv, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.beta_reduce, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_var_reordering, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.exists_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_unused_vars, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_merge_prenex, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_miniscope_and, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_miniscope_or, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_miniscope_ite, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_var_elim_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.quant_dt_split, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_split, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_inst, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_collapse_selector, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_collapse_tester, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_collapse_tester_singleton, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_cons_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_cons_eq_clash, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_cycle, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_collapse_updater, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.dt_updater_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_div_total_zero_real, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_div_total_zero_int, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_div_total, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_div_total_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_div_total_zero, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_div_total_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_mod_total, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_mod_total_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_mod_total_zero, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_mod_total_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_div_total_over_mod, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_elim_gt, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_elim_lt, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_elim_int_gt, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_elim_int_lt, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_elim_leq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_leq_norm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_geq_tighten, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_geq_norm1_int, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_geq_norm1_real, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_eq_elim_real, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_eq_elim_int, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_to_int_elim_to_real, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_is_int_elim_to_real, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_div_int_to_real, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_div_total_int_to_real, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mod_over_mod_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mod_over_mod, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_mod_over_mod_mult, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_eq_conflict, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_int_geq_tighten, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_divisible_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_abs_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_abs_int_gt, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_abs_real_gt, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_geq_ite_lift, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_leq_ite_lift, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_min_lt1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_min_lt2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_max_geq1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.arith_max_geq2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.array_read_over_write, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.array_read_over_write2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.array_store_overwrite, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.array_store_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.array_read_over_write_split, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.array_store_swap, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_double_not_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_not_true, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_not_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_eq_true, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_eq_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_eq_nrefl, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_impl_false1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_impl_false2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_impl_true1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_impl_true2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_impl_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_dual_impl_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_and_conf, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_and_conf2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_or_taut, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_or_taut2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_or_de_morgan, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_implies_de_morgan, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_and_de_morgan, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_or_and_distrib, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_implies_or_distrib, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_xor_refl, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_xor_nrefl, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_xor_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_xor_true, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_xor_comm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_xor_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_not_xor_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_not_eq_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_not_eq_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_neg_branch, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_then_true, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_else_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_then_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_else_true, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_then_lookahead_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_else_lookahead_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_then_lookahead_not_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_else_lookahead_not_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_expand, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bool_not_ite_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_true_cond, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_false_cond, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_not_cond, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_eq_branch, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_then_lookahead, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_else_lookahead, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_then_neg_lookahead, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.ite_else_neg_lookahead, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_concat_extract_merge, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_extract, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_whole, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_concat_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_concat_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_concat_3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_concat_4, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_eq_extract_elim1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_eq_extract_elim2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_eq_extract_elim3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_not, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_sign_extend_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_sign_extend_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_sign_extend_3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_not_xor, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_and_simplify_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_and_simplify_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_or_simplify_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_or_simplify_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_simplify_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_simplify_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_simplify_3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ult_add_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_mult_slt_mult_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_mult_slt_mult_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_commutative_xor, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_commutative_comp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_zero_extend_eliminate_0, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sign_extend_eliminate_0, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_not_neq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ult_ones, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_concat_merge_const, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_commutative_add, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sub_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_width_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_width_one_not, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_eq_xor_solve, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_eq_not_solve, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ugt_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_uge_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sgt_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sge_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sle_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_redor_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_redand_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ule_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_comp_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_rotate_left_eliminate_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_rotate_left_eliminate_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_rotate_right_eliminate_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_rotate_right_eliminate_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_nand_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_nor_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xnor_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sdiv_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_zero_extend_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_uaddo_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_saddo_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sdivo_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_smod_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_srem_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_usubo_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ssubo_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_nego_eliminate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_equal_children, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_const_cond_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_const_cond_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_const_children_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_const_children_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_equal_cond_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_equal_cond_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_equal_cond_3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_merge_then_if, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_merge_else_if, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_merge_then_else, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ite_merge_else_else, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_shl_by_const_0, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_shl_by_const_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_shl_by_const_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_lshr_by_const_0, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_lshr_by_const_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_lshr_by_const_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ashr_by_const_0, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ashr_by_const_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ashr_by_const_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_and_concat_pullup, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_or_concat_pullup, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_concat_pullup, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_and_concat_pullup2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_or_concat_pullup2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_concat_pullup2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_and_concat_pullup3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_or_concat_pullup3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_concat_pullup3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_duplicate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_ones, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_xor_not, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_not_idemp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ult_zero_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ult_zero_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ult_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_lt_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ule_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ule_zero, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_zero_ule, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sle_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ule_max, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_not_ult, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_mult_pow2_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_mult_pow2_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_mult_pow2_2b, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_extract_mult_leading_bit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_udiv_pow2_not_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_udiv_zero, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_udiv_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_urem_pow2_not_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_urem_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_urem_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_shl_zero, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_lshr_zero, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ashr_zero, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ugt_urem, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_ult_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_merge_sign_extend_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_merge_sign_extend_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sign_extend_eq_const_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sign_extend_eq_const_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_zero_extend_eq_const_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_zero_extend_eq_const_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_zero_extend_ult_const_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_zero_extend_ult_const_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sign_extend_ult_const_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sign_extend_ult_const_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sign_extend_ult_const_3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.bv_sign_extend_ult_const_4, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_eq_singleton_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_member_singleton, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_member_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_subset_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_insert_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_union_comm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_inter_comm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_inter_emp1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_inter_emp2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_minus_emp1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_minus_emp2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_union_emp1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_union_emp2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_inter_member, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_minus_member, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_union_member, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_choose_singleton, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_minus_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_union_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_inter_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_is_empty_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.sets_is_singleton_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_ctn_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_ctn_full_false1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_ctn_full_false2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_len_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_empty_str, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_empty_range, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_empty_start, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_empty_start_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_substr_start_geq_len, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_eq_empty, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_z_eq_empty_leq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_eq_empty_leq_len, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_len_replace_inv, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_len_replace_all_inv, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_len_update_inv, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_update_oob, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_update_rev, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_update_fit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_update_concat_fit0, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_update_concat_fit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_update_in_first_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_len_substr_in_range, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_clash, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_clash_rev, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_clash2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_clash2_rev, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_unify, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_unify_rev, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_unify_base, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_concat_unify_base_rev, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_prefixof_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_suffixof_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_prefixof_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_suffixof_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_prefixof_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_suffixof_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_combine1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_combine2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_combine3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_combine4, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_concat1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_concat2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_replace, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_full, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_full_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_refl, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_concat_find, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_concat_find_contra, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_split_char, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_leq_len_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_char, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_at_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_id, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_prefix, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_prefix_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_no_contains, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_find_base, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_find_first_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_empty, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_one_pre, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_find_pre, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_all_no_contains, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_all_find_pre, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_all_find, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_all_empty, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_all_id, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_all_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_re_none, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_re_all_none, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_len_concat_rec, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_len_eq_zero_concat_rec, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_len_eq_zero_base, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_no_contains, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_oob, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_oob2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_contains_pre, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_contains_concat_pre, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_prefix_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_len_oob, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_len_oob2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_find_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_eq_irr, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_re_none, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_indexof_re_emp_re, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_lower_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_upper_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_lower_upper, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_lower_idem, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_upper_lower, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_upper_idem, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_lower_len, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_upper_len, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_lower_from_int, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_upper_from_int, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_to_int_concat_neg_one, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_is_digit_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_leq_empty, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_leq_empty_eq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_leq_concat_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_leq_concat_true, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_leq_concat_base_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_leq_concat_base_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_lt_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_from_int_no_ctn_nondigit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_ctn_contra, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_ctn, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_dual_ctn, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_dual_ctn_false, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_self_ctn_simp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_replace_emp_ctn_src, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_char_start_eq_len, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_repl_char, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_repl_self_tgt_char, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_repl_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_contains_repl_tgt, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_len_id, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_src_tgt_no_ctn, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_tgt_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_tgt_no_ctn, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_src_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_src_inv_no_ctn1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_src_inv_no_ctn2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_src_inv_no_ctn3, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_dual_self, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_dual_ite1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_dual_ite2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_repl_repl_lookahead_id_simp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_all_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_opt_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_diff_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_plus_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_repeat_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_concat_star_swap, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_concat_star_repeat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_concat_star_nullable1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_concat_star_nullable2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_concat_merge, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_union_all, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_union_const_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_inter_all, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_star_none, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_star_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_star_star, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_range_refl, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_range_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_range_non_singleton_1, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_range_non_singleton_2, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_star_union_char, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_star_union_drop_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_loop_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_loop_star, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_inter_cstring, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_inter_cstring_neg, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_len_include, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_len_include_pre, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_substr_len_norm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_len_rev, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_rev_rev, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_rev_concat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_repl_self_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_repl_no_change, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_repl_tgt_eq_len, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_repl_len_one_emp_prefix, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_repl_emp_tgt_nemp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_repl_nemp_src_emp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_eq_repl_self_src, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_len_unit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_nth_unit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_nth_concat_unit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_nth_concat_unit_gen, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.seq_rev_unit, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_in_empty, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_in_sigma, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_in_sigma_star, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_in_cstring, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.re_in_comp, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_union_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_inter_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_range_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_contains, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_from_int_nemp_dig_range, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.str_in_re_from_int_dig_range, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.eq_refl, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.eq_symm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.eq_cond_deq, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.eq_ite_lift, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.distinct_binary_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_bv2nat_int2bv, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_bv2nat_int2bv_extend, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_bv2nat_int2bv_extract, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_int2bv_bv2nat, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_bv2nat_geq_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_int2bv_bvult_equiv, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_int2bv_bvule_equiv, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.uf_sbv_to_int_elim, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.evaluate, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.distinct_values, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.aci_norm, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.absorb, h => by
    simp only [enc_CRule]
    unfold dec_CRule
    rfl
  | Eo.CRule.distinct_card_conflict, h => by
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

theorem inv_CRule_process_scope {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eprocess_5fscope ts) (he : emb_CRule x) :
    x = Eo.CRule.process_scope ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esplit ts) (he : emb_CRule x) :
    x = Eo.CRule.split ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_resolution {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eresolution ts) (he : emb_CRule x) :
    x = Eo.CRule.resolution ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_chain_resolution {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fresolution ts) (he : emb_CRule x) :
    x = Eo.CRule.chain_resolution ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_chain_m_resolution {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution ts) (he : emb_CRule x) :
    x = Eo.CRule.chain_m_resolution ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_factoring {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2efactoring ts) (he : emb_CRule x) :
    x = Eo.CRule.factoring ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_reordering {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ereordering ts) (he : emb_CRule x) :
    x = Eo.CRule.reordering ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_eq_resolve {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fresolve ts) (he : emb_CRule x) :
    x = Eo.CRule.eq_resolve ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_modus_ponens {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2emodus_5fponens ts) (he : emb_CRule x) :
    x = Eo.CRule.modus_ponens ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_not_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.not_not_elim ∧ ts = [] := by
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

theorem inv_CRule_and_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eand_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.and_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_and_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eand_5fintro ts) (he : emb_CRule x) :
    x = Eo.CRule.and_intro ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_or_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5for_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.not_or_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_implies_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eimplies_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.implies_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_implies_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_implies_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_implies_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_implies_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_equiv_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.equiv_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_equiv_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.equiv_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_equiv_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_equiv_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_equiv_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_equiv_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_xor_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.xor_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_xor_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.xor_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_xor_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_xor_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_xor_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_xor_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_ite_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_ite_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_ite_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.not_ite_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_not_and {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fand ts) (he : emb_CRule x) :
    x = Eo.CRule.not_and ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_and_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_and_pos ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_and_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_and_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_or_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_or_pos ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_or_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_or_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_implies_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_implies_pos ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_implies_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_implies_neg1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_implies_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_implies_neg2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_equiv_pos1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_equiv_pos1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_equiv_pos2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_equiv_pos2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_equiv_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_equiv_neg1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_equiv_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_equiv_neg2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_xor_pos1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_xor_pos1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_xor_pos2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_xor_pos2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_xor_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_xor_neg1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_xor_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_xor_neg2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_ite_pos1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_ite_pos1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_ite_pos2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_ite_pos2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_ite_pos3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_ite_pos3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_ite_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_ite_neg1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_ite_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_ite_neg2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_cnf_ite_neg3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 ts) (he : emb_CRule x) :
    x = Eo.CRule.cnf_ite_neg3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arrays_read_over_write {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite ts) (he : emb_CRule x) :
    x = Eo.CRule.arrays_read_over_write ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arrays_read_over_write_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra ts) (he : emb_CRule x) :
    x = Eo.CRule.arrays_read_over_write_contra ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arrays_read_over_write_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.arrays_read_over_write_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arrays_ext {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fext ts) (he : emb_CRule x) :
    x = Eo.CRule.arrays_ext ∧ ts = [] := by
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

theorem inv_CRule_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econg ts) (he : emb_CRule x) :
    x = Eo.CRule.cong ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_nary_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enary_5fcong ts) (he : emb_CRule x) :
    x = Eo.CRule.nary_cong ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_pairwise_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2epairwise_5fcong ts) (he : emb_CRule x) :
    x = Eo.CRule.pairwise_cong ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_true_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5fintro ts) (he : emb_CRule x) :
    x = Eo.CRule.true_intro ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_true_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.true_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_false_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5fintro ts) (he : emb_CRule x) :
    x = Eo.CRule.false_intro ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_false_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.false_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ho_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eho_5fcong ts) (he : emb_CRule x) :
    x = Eo.CRule.ho_cong ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_distinct_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.distinct_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_distinct_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue ts) (he : emb_CRule x) :
    x = Eo.CRule.distinct_true ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_distinct_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.distinct_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_sum_ub {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_sum_ub ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mult_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mult_pos ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mult_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mult_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_trichotomy {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_trichotomy ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_int_tight_ub {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub ts) (he : emb_CRule x) :
    x = Eo.CRule.int_tight_ub ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_int_tight_lb {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb ts) (he : emb_CRule x) :
    x = Eo.CRule.int_tight_lb ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mult_tangent {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mult_tangent ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mult_sign {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mult_sign ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mult_abs_comparison {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mult_abs_comparison ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_reduction {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5freduction ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_reduction ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_poly_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_poly_norm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_poly_norm_rel {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_poly_norm_rel ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_repeat_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_repeat_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_smulo_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_smulo_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_umulo_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_umulo_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_bitwise_slicing {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_bitwise_slicing ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_bitblast_step {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_bitblast_step ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_poly_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_poly_norm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_poly_norm_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_poly_norm_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_length_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos ts) (he : emb_CRule x) :
    x = Eo.CRule.string_length_pos ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_length_non_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty ts) (he : emb_CRule x) :
    x = Eo.CRule.string_length_non_empty ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_concat_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.concat_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_concat_unify {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5funify ts) (he : emb_CRule x) :
    x = Eo.CRule.concat_unify ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_concat_csplit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit ts) (he : emb_CRule x) :
    x = Eo.CRule.concat_csplit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_concat_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fsplit ts) (he : emb_CRule x) :
    x = Eo.CRule.concat_split ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_concat_lprop {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5flprop ts) (he : emb_CRule x) :
    x = Eo.CRule.concat_lprop ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_concat_cprop {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcprop ts) (he : emb_CRule x) :
    x = Eo.CRule.concat_cprop ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_decompose {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fdecompose ts) (he : emb_CRule x) :
    x = Eo.CRule.string_decompose ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_exists_string_length {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength ts) (he : emb_CRule x) :
    x = Eo.CRule.exists_string_length ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_code_inj {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj ts) (he : emb_CRule x) :
    x = Eo.CRule.string_code_inj ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_seq_unit_inj {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj ts) (he : emb_CRule x) :
    x = Eo.CRule.string_seq_unit_inj ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_inter {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter ts) (he : emb_CRule x) :
    x = Eo.CRule.re_inter ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.re_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_unfold_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos ts) (he : emb_CRule x) :
    x = Eo.CRule.re_unfold_pos ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_unfold_neg_concat_fixed {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed ts) (he : emb_CRule x) :
    x = Eo.CRule.re_unfold_neg_concat_fixed ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_unfold_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.re_unfold_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_ext {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fext ts) (he : emb_CRule x) :
    x = Eo.CRule.string_ext ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_reduction {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5freduction ts) (he : emb_CRule x) :
    x = Eo.CRule.string_reduction ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_string_eager_reduction {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction ts) (he : emb_CRule x) :
    x = Eo.CRule.string_eager_reduction ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_string_pred_entail {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_string_pred_entail ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_string_pred_safe_approx {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_string_pred_safe_approx ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_eval ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_consume {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_consume ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_loop_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_loop_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_eq_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_eq_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_inter_inclusion {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion ts) (he : emb_CRule x) :
    x = Eo.CRule.re_inter_inclusion ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_union_inclusion {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion ts) (he : emb_CRule x) :
    x = Eo.CRule.re_union_inclusion ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_concat_star_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_concat_star_char ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_sigma {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_sigma ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_sigma_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_sigma_star ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_ctn_multiset_subset {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset ts) (he : emb_CRule x) :
    x = Eo.CRule.str_ctn_multiset_subset ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_overlap_split_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn ts) (he : emb_CRule x) :
    x = Eo.CRule.str_overlap_split_ctn ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_overlap_endpoints_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn ts) (he : emb_CRule x) :
    x = Eo.CRule.str_overlap_endpoints_ctn ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_overlap_endpoints_indexof {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof ts) (he : emb_CRule x) :
    x = Eo.CRule.str_overlap_endpoints_indexof ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_overlap_endpoints_replace {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace ts) (he : emb_CRule x) :
    x = Eo.CRule.str_overlap_endpoints_replace ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_re_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_re_eval ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_re_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_re_eval ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_re_all_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_re_all_eval ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_eval_op {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_eval_op ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_singleton_inj {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_singleton_inj ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_ext {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fext ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_ext ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_choose_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_choose_member ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_eval_op {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_eval_op ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ubv_to_int_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange ts) (he : emb_CRule x) :
    x = Eo.CRule.ubv_to_int_range ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ubv_to_int_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.ubv_to_int_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_int_to_bv_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.int_to_bv_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_instantiate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2einstantiate ts) (he : emb_CRule x) :
    x = Eo.CRule.instantiate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_skolemize {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eskolemize ts) (he : emb_CRule x) :
    x = Eo.CRule.skolemize ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_skolem_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eskolem_5fintro ts) (he : emb_CRule x) :
    x = Eo.CRule.skolem_intro ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_alpha_equiv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv ts) (he : emb_CRule x) :
    x = Eo.CRule.alpha_equiv ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_beta_reduce {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebeta_5freduce ts) (he : emb_CRule x) :
    x = Eo.CRule.beta_reduce ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_var_reordering {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_var_reordering ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_exists_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.exists_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_unused_vars {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_unused_vars ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_merge_prenex {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_merge_prenex ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_miniscope_and {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_miniscope_and ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_miniscope_or {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_miniscope_or ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_miniscope_ite {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_miniscope_ite ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_var_elim_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_var_elim_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_quant_dt_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit ts) (he : emb_CRule x) :
    x = Eo.CRule.quant_dt_split ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fsplit ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_split ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_inst {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5finst ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_inst ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_collapse_selector {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_collapse_selector ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_collapse_tester {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_collapse_tester ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_collapse_tester_singleton {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_collapse_tester_singleton ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_cons_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_cons_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_cons_eq_clash {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_cons_eq_clash ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_cycle {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcycle ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_cycle ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_collapse_updater {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_collapse_updater ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_dt_updater_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.dt_updater_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_div_total_zero_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_div_total_zero_real ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_div_total_zero_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_div_total_zero_int ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_div_total {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_div_total ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_div_total_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_div_total_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_div_total_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_div_total_zero ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_div_total_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_div_total_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_mod_total {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_mod_total ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_mod_total_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_mod_total_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_mod_total_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_mod_total_zero ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_mod_total_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_mod_total_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_div_total_over_mod {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_div_total_over_mod ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_elim_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_elim_gt ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_elim_lt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_elim_lt ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_elim_int_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_elim_int_gt ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_elim_int_lt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_elim_int_lt ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_elim_leq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_elim_leq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_leq_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_leq_norm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_geq_tighten {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_geq_tighten ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_geq_norm1_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_geq_norm1_int ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_geq_norm1_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_geq_norm1_real ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_eq_elim_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_eq_elim_real ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_eq_elim_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_eq_elim_int ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_to_int_elim_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_to_int_elim_to_real ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_is_int_elim_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_is_int_elim_to_real ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_div_int_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_div_int_to_real ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_div_total_int_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_div_total_int_to_real ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mod_over_mod_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mod_over_mod_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mod_over_mod {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mod_over_mod ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_mod_over_mod_mult {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_mod_over_mod_mult ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_eq_conflict {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_eq_conflict ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_int_geq_tighten {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_int_geq_tighten ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_divisible_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_divisible_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_abs_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_abs_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_abs_int_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_abs_int_gt ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_abs_real_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_abs_real_gt ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_geq_ite_lift {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_geq_ite_lift ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_leq_ite_lift {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_leq_ite_lift ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_min_lt1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_min_lt1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_min_lt2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_min_lt2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_max_geq1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_max_geq1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_arith_max_geq2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 ts) (he : emb_CRule x) :
    x = Eo.CRule.arith_max_geq2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_array_read_over_write {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite ts) (he : emb_CRule x) :
    x = Eo.CRule.array_read_over_write ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_array_read_over_write2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 ts) (he : emb_CRule x) :
    x = Eo.CRule.array_read_over_write2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_array_store_overwrite {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite ts) (he : emb_CRule x) :
    x = Eo.CRule.array_store_overwrite ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_array_store_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.array_store_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_array_read_over_write_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit ts) (he : emb_CRule x) :
    x = Eo.CRule.array_read_over_write_split ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_array_store_swap {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap ts) (he : emb_CRule x) :
    x = Eo.CRule.array_store_swap ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_double_not_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_double_not_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_not_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_not_true ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_not_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_not_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_eq_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_eq_true ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_eq_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_eq_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_eq_nrefl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_eq_nrefl ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_impl_false1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_impl_false1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_impl_false2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_impl_false2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_impl_true1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_impl_true1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_impl_true2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_impl_true2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_impl_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_impl_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_dual_impl_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_dual_impl_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_and_conf {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_and_conf ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_and_conf2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_and_conf2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_or_taut {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_or_taut ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_or_taut2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_or_taut2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_or_de_morgan {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_or_de_morgan ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_implies_de_morgan {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_implies_de_morgan ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_and_de_morgan {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_and_de_morgan ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_or_and_distrib {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_or_and_distrib ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_implies_or_distrib {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_implies_or_distrib ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_xor_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_xor_refl ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_xor_nrefl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_xor_nrefl ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_xor_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_xor_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_xor_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_xor_true ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_xor_comm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_xor_comm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_xor_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_xor_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_not_xor_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_not_xor_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_not_eq_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_not_eq_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_not_eq_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_not_eq_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_neg_branch {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_neg_branch ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_then_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_then_true ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_else_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_else_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_then_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_then_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_else_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_else_true ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_then_lookahead_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_then_lookahead_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_else_lookahead_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_else_lookahead_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_then_lookahead_not_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_then_lookahead_not_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_else_lookahead_not_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_else_lookahead_not_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_expand {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fexpand ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_expand ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bool_not_ite_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.bool_not_ite_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_true_cond {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_true_cond ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_false_cond {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_false_cond ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_not_cond {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_not_cond ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_eq_branch {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_eq_branch ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_then_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_then_lookahead ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_else_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_else_lookahead ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_then_neg_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_then_neg_lookahead ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_ite_else_neg_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead ts) (he : emb_CRule x) :
    x = Eo.CRule.ite_else_neg_lookahead ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_concat_extract_merge {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_concat_extract_merge ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_extract {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_extract ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_whole {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_whole ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_concat_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_concat_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_concat_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_concat_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_concat_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_concat_3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_concat_4 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_concat_4 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_eq_extract_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_eq_extract_elim1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_eq_extract_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_eq_extract_elim2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_eq_extract_elim3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_eq_extract_elim3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_not {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_not ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_sign_extend_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_sign_extend_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_sign_extend_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_sign_extend_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_sign_extend_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_sign_extend_3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_not_xor {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_not_xor ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_and_simplify_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_and_simplify_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_and_simplify_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_and_simplify_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_or_simplify_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_or_simplify_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_or_simplify_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_or_simplify_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_simplify_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_simplify_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_simplify_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_simplify_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_simplify_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_simplify_3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ult_add_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ult_add_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_mult_slt_mult_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_mult_slt_mult_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_mult_slt_mult_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_mult_slt_mult_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_commutative_xor {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_commutative_xor ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_commutative_comp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_commutative_comp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_zero_extend_eliminate_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_zero_extend_eliminate_0 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sign_extend_eliminate_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sign_extend_eliminate_0 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_not_neq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_not_neq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ult_ones {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ult_ones ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_concat_merge_const {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_concat_merge_const ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_commutative_add {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_commutative_add ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sub_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sub_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_width_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_width_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_width_one_not {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_width_one_not ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_eq_xor_solve {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_eq_xor_solve ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_eq_not_solve {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_eq_not_solve ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ugt_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ugt_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_uge_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_uge_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sgt_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sgt_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sge_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sge_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sle_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sle_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_redor_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_redor_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_redand_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_redand_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ule_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ule_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_comp_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_comp_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_rotate_left_eliminate_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_rotate_left_eliminate_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_rotate_left_eliminate_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_rotate_left_eliminate_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_rotate_right_eliminate_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_rotate_right_eliminate_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_rotate_right_eliminate_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_rotate_right_eliminate_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_nand_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_nand_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_nor_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_nor_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xnor_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xnor_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sdiv_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sdiv_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_zero_extend_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_zero_extend_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_uaddo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_uaddo_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_saddo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_saddo_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sdivo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sdivo_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_smod_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_smod_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_srem_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_srem_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_usubo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_usubo_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ssubo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ssubo_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_nego_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_nego_eliminate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_equal_children {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_equal_children ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_const_cond_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_const_cond_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_const_cond_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_const_cond_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_const_children_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_const_children_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_const_children_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_const_children_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_equal_cond_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_equal_cond_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_equal_cond_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_equal_cond_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_equal_cond_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_equal_cond_3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_merge_then_if {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_merge_then_if ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_merge_else_if {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_merge_else_if ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_merge_then_else {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_merge_then_else ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ite_merge_else_else {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ite_merge_else_else ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_shl_by_const_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_shl_by_const_0 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_shl_by_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_shl_by_const_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_shl_by_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_shl_by_const_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_lshr_by_const_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_lshr_by_const_0 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_lshr_by_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_lshr_by_const_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_lshr_by_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_lshr_by_const_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ashr_by_const_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ashr_by_const_0 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ashr_by_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ashr_by_const_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ashr_by_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ashr_by_const_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_and_concat_pullup {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_and_concat_pullup ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_or_concat_pullup {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_or_concat_pullup ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_concat_pullup {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_concat_pullup ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_and_concat_pullup2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_and_concat_pullup2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_or_concat_pullup2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_or_concat_pullup2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_concat_pullup2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_concat_pullup2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_and_concat_pullup3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_and_concat_pullup3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_or_concat_pullup3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_or_concat_pullup3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_concat_pullup3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_concat_pullup3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_duplicate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_duplicate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_ones {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_ones ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_xor_not {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_xor_not ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_not_idemp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_not_idemp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ult_zero_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ult_zero_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ult_zero_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ult_zero_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ult_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ult_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_lt_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_lt_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ule_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ule_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ule_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ule_zero ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_zero_ule {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_zero_ule ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sle_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sle_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ule_max {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ule_max ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_not_ult {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_not_ult ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_mult_pow2_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_mult_pow2_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_mult_pow2_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_mult_pow2_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_mult_pow2_2b {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_mult_pow2_2b ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_extract_mult_leading_bit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_extract_mult_leading_bit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_udiv_pow2_not_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_udiv_pow2_not_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_udiv_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_udiv_zero ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_udiv_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_udiv_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_urem_pow2_not_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_urem_pow2_not_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_urem_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_urem_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_urem_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_urem_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_shl_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_shl_zero ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_lshr_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_lshr_zero ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ashr_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ashr_zero ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ugt_urem {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ugt_urem ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_ult_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_ult_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_merge_sign_extend_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_merge_sign_extend_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_merge_sign_extend_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_merge_sign_extend_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sign_extend_eq_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sign_extend_eq_const_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sign_extend_eq_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sign_extend_eq_const_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_zero_extend_eq_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_zero_extend_eq_const_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_zero_extend_eq_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_zero_extend_eq_const_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_zero_extend_ult_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_zero_extend_ult_const_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_zero_extend_ult_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_zero_extend_ult_const_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sign_extend_ult_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sign_extend_ult_const_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sign_extend_ult_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sign_extend_ult_const_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sign_extend_ult_const_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sign_extend_ult_const_3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_bv_sign_extend_ult_const_4 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 ts) (he : emb_CRule x) :
    x = Eo.CRule.bv_sign_extend_ult_const_4 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_eq_singleton_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_eq_singleton_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_member_singleton {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_member_singleton ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_member_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_member_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_subset_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_subset_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_insert_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_insert_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_union_comm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_union_comm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_inter_comm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_inter_comm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_inter_emp1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_inter_emp1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_inter_emp2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_inter_emp2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_minus_emp1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_minus_emp1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_minus_emp2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_minus_emp2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_union_emp1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_union_emp1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_union_emp2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_union_emp2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_inter_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_inter_member ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_minus_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_minus_member ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_union_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_union_member ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_choose_singleton {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_choose_singleton ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_minus_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_minus_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_union_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_union_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_inter_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_inter_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_is_empty_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_is_empty_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_sets_is_singleton_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.sets_is_singleton_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_ctn_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_ctn_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_ctn_full_false1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_ctn_full_false1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_ctn_full_false2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_ctn_full_false2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_len_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_len_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_empty_str {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_empty_str ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_empty_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_empty_range ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_empty_start {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_empty_start ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_empty_start_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_empty_start_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_substr_start_geq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_substr_start_geq_len ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_eq_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_eq_empty ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_z_eq_empty_leq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_z_eq_empty_leq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_eq_empty_leq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_eq_empty_leq_len ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_len_replace_inv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv ts) (he : emb_CRule x) :
    x = Eo.CRule.str_len_replace_inv ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_len_replace_all_inv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv ts) (he : emb_CRule x) :
    x = Eo.CRule.str_len_replace_all_inv ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_len_update_inv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv ts) (he : emb_CRule x) :
    x = Eo.CRule.str_len_update_inv ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_update_oob {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob ts) (he : emb_CRule x) :
    x = Eo.CRule.str_update_oob ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_update_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev ts) (he : emb_CRule x) :
    x = Eo.CRule.str_update_rev ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_update_fit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit ts) (he : emb_CRule x) :
    x = Eo.CRule.str_update_fit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_update_concat_fit0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_update_concat_fit0 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_update_concat_fit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit ts) (he : emb_CRule x) :
    x = Eo.CRule.str_update_concat_fit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_update_in_first_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.str_update_in_first_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_len_substr_in_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange ts) (he : emb_CRule x) :
    x = Eo.CRule.str_len_substr_in_range ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_clash {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_clash ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_clash_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_clash_rev ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_clash2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_clash2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_clash2_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_clash2_rev ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_unify {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_unify ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_unify_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_unify_rev ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_unify_base {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_unify_base ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_concat_unify_base_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev ts) (he : emb_CRule x) :
    x = Eo.CRule.str_concat_unify_base_rev ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_prefixof_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_prefixof_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_suffixof_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_suffixof_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_prefixof_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.str_prefixof_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_suffixof_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.str_suffixof_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_prefixof_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.str_prefixof_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_suffixof_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.str_suffixof_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_combine1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_combine1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_combine2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_combine2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_combine3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_combine3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_combine4 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_combine4 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_concat1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_concat1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_concat2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_concat2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_replace {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_replace ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_full {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_full ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_full_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_full_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_refl ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_concat_find {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_concat_find ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_concat_find_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_concat_find_contra ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_split_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_split_char ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_leq_len_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_leq_len_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_char ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_at_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_at_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_id {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_id ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_prefix {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_prefix ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_prefix_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_prefix_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_no_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_no_contains ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_find_base {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_find_base ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_find_first_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_find_first_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_empty ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_one_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_one_pre ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_find_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_find_pre ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_all_no_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_all_no_contains ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_all_find_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_all_find_pre ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_all_find {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_all_find ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_all_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_all_empty ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_all_id {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_all_id ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_all_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_all_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_re_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_re_none ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_re_all_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_re_all_none ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_len_concat_rec {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec ts) (he : emb_CRule x) :
    x = Eo.CRule.str_len_concat_rec ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_len_eq_zero_concat_rec {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec ts) (he : emb_CRule x) :
    x = Eo.CRule.str_len_eq_zero_concat_rec ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_len_eq_zero_base {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase ts) (he : emb_CRule x) :
    x = Eo.CRule.str_len_eq_zero_base ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_no_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_no_contains ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_oob {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_oob ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_oob2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_oob2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_contains_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_contains_pre ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_contains_concat_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_contains_concat_pre ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_prefix_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_prefix_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_len_oob {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_len_oob ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_len_oob2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_len_oob2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_find_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_find_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_eq_irr {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_eq_irr ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_re_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_re_none ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_indexof_re_emp_re {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre ts) (he : emb_CRule x) :
    x = Eo.CRule.str_indexof_re_emp_re ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_lower_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_lower_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_upper_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_upper_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_lower_upper {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_lower_upper ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_lower_idem {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_lower_idem ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_upper_lower {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_upper_lower ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_upper_idem {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_upper_idem ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_lower_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_lower_len ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_upper_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_upper_len ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_lower_from_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_lower_from_int ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_upper_from_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_upper_from_int ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_to_int_concat_neg_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone ts) (he : emb_CRule x) :
    x = Eo.CRule.str_to_int_concat_neg_one ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_is_digit_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_is_digit_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_leq_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty ts) (he : emb_CRule x) :
    x = Eo.CRule.str_leq_empty ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_leq_empty_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq ts) (he : emb_CRule x) :
    x = Eo.CRule.str_leq_empty_eq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_leq_concat_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.str_leq_concat_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_leq_concat_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue ts) (he : emb_CRule x) :
    x = Eo.CRule.str_leq_concat_true ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_leq_concat_base_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_leq_concat_base_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_leq_concat_base_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_leq_concat_base_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_lt_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_lt_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_from_int_no_ctn_nondigit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit ts) (he : emb_CRule x) :
    x = Eo.CRule.str_from_int_no_ctn_nondigit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_ctn_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_ctn_contra ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_ctn ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_dual_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_dual_ctn ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_dual_ctn_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_dual_ctn_false ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_self_ctn_simp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_self_ctn_simp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_replace_emp_ctn_src {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc ts) (he : emb_CRule x) :
    x = Eo.CRule.str_replace_emp_ctn_src ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_char_start_eq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_char_start_eq_len ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_repl_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_repl_char ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_repl_self_tgt_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_repl_self_tgt_char ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_repl_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_repl_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_contains_repl_tgt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt ts) (he : emb_CRule x) :
    x = Eo.CRule.str_contains_repl_tgt ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_len_id {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_len_id ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_src_tgt_no_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_src_tgt_no_ctn ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_tgt_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_tgt_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_tgt_no_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_tgt_no_ctn ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_src_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_src_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_src_inv_no_ctn1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_src_inv_no_ctn1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_src_inv_no_ctn2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_src_inv_no_ctn2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_src_inv_no_ctn3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_src_inv_no_ctn3 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_dual_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_dual_self ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_dual_ite1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_dual_ite1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_dual_ite2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_dual_ite2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_repl_repl_lookahead_id_simp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp ts) (he : emb_CRule x) :
    x = Eo.CRule.str_repl_repl_lookahead_id_simp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_all_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_all_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_opt_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_opt_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_diff_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_diff_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_plus_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_plus_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_repeat_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_repeat_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_concat_star_swap {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap ts) (he : emb_CRule x) :
    x = Eo.CRule.re_concat_star_swap ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_concat_star_repeat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat ts) (he : emb_CRule x) :
    x = Eo.CRule.re_concat_star_repeat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_concat_star_nullable1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 ts) (he : emb_CRule x) :
    x = Eo.CRule.re_concat_star_nullable1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_concat_star_nullable2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 ts) (he : emb_CRule x) :
    x = Eo.CRule.re_concat_star_nullable2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_concat_merge {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge ts) (he : emb_CRule x) :
    x = Eo.CRule.re_concat_merge ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_union_all {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall ts) (he : emb_CRule x) :
    x = Eo.CRule.re_union_all ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_union_const_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.re_union_const_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_inter_all {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall ts) (he : emb_CRule x) :
    x = Eo.CRule.re_inter_all ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_star_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone ts) (he : emb_CRule x) :
    x = Eo.CRule.re_star_none ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_star_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.re_star_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_star_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar ts) (he : emb_CRule x) :
    x = Eo.CRule.re_star_star ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_range_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl ts) (he : emb_CRule x) :
    x = Eo.CRule.re_range_refl ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_range_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.re_range_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_range_non_singleton_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 ts) (he : emb_CRule x) :
    x = Eo.CRule.re_range_non_singleton_1 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_range_non_singleton_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 ts) (he : emb_CRule x) :
    x = Eo.CRule.re_range_non_singleton_2 ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_star_union_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar ts) (he : emb_CRule x) :
    x = Eo.CRule.re_star_union_char ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_star_union_drop_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.re_star_union_drop_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_loop_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.re_loop_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_loop_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar ts) (he : emb_CRule x) :
    x = Eo.CRule.re_loop_star ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_inter_cstring {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring ts) (he : emb_CRule x) :
    x = Eo.CRule.re_inter_cstring ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_inter_cstring_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg ts) (he : emb_CRule x) :
    x = Eo.CRule.re_inter_cstring_neg ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_len_include {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_len_include ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_len_include_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_len_include_pre ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_substr_len_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm ts) (he : emb_CRule x) :
    x = Eo.CRule.str_substr_len_norm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_len_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_len_rev ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_rev_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_rev_rev ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_rev_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_rev_concat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_repl_self_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_repl_self_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_repl_no_change {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_repl_no_change ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_repl_tgt_eq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_repl_tgt_eq_len ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_repl_len_one_emp_prefix {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_repl_len_one_emp_prefix ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_repl_emp_tgt_nemp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_repl_emp_tgt_nemp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_repl_nemp_src_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_repl_nemp_src_emp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_eq_repl_self_src {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc ts) (he : emb_CRule x) :
    x = Eo.CRule.str_eq_repl_self_src ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_len_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_len_unit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_nth_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_nth_unit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_nth_concat_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_nth_concat_unit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_nth_concat_unit_gen {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_nth_concat_unit_gen ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_seq_rev_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit ts) (he : emb_CRule x) :
    x = Eo.CRule.seq_rev_unit ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_in_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty ts) (he : emb_CRule x) :
    x = Eo.CRule.re_in_empty ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_in_sigma {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma ts) (he : emb_CRule x) :
    x = Eo.CRule.re_in_sigma ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_in_sigma_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar ts) (he : emb_CRule x) :
    x = Eo.CRule.re_in_sigma_star ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_in_cstring {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring ts) (he : emb_CRule x) :
    x = Eo.CRule.re_in_cstring ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_re_in_comp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp ts) (he : emb_CRule x) :
    x = Eo.CRule.re_in_comp ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_union_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_union_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_inter_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_inter_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_range_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_range_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_contains ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_from_int_nemp_dig_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_from_int_nemp_dig_range ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_str_in_re_from_int_dig_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange ts) (he : emb_CRule x) :
    x = Eo.CRule.str_in_re_from_int_dig_range ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_eq_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5frefl ts) (he : emb_CRule x) :
    x = Eo.CRule.eq_refl ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_eq_symm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fsymm ts) (he : emb_CRule x) :
    x = Eo.CRule.eq_symm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_eq_cond_deq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq ts) (he : emb_CRule x) :
    x = Eo.CRule.eq_cond_deq ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_eq_ite_lift {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift ts) (he : emb_CRule x) :
    x = Eo.CRule.eq_ite_lift ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_distinct_binary_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.distinct_binary_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_bv2nat_int2bv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_bv2nat_int2bv ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_bv2nat_int2bv_extend {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_bv2nat_int2bv_extend ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_bv2nat_int2bv_extract {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_bv2nat_int2bv_extract ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_int2bv_bv2nat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_int2bv_bv2nat ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_bv2nat_geq_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_bv2nat_geq_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_int2bv_bvult_equiv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_int2bv_bvult_equiv ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_int2bv_bvule_equiv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_int2bv_bvule_equiv ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_uf_sbv_to_int_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim ts) (he : emb_CRule x) :
    x = Eo.CRule.uf_sbv_to_int_elim ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_evaluate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eevaluate ts) (he : emb_CRule x) :
    x = Eo.CRule.evaluate ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_distinct_values {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues ts) (he : emb_CRule x) :
    x = Eo.CRule.distinct_values ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_aci_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eaci_5fnorm ts) (he : emb_CRule x) :
    x = Eo.CRule.aci_norm ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_absorb {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eabsorb ts) (he : emb_CRule x) :
    x = Eo.CRule.absorb ∧ ts = [] := by
  have hd := dec_enc_CRule x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_CRule at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_CRule at hd
    cases hd

theorem inv_CRule_distinct_card_conflict {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict ts) (he : emb_CRule x) :
    x = Eo.CRule.distinct_card_conflict ∧ ts = [] := by
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
  case «process_scope» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «split» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «resolution» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «chain_resolution» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «chain_m_resolution» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «factoring» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «reordering» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «eq_resolve» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «modus_ponens» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_not_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «contra» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «and_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «and_intro» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_or_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «implies_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_implies_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_implies_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «equiv_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «equiv_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_equiv_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_equiv_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «xor_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «xor_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_xor_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_xor_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_ite_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_ite_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not_and» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_and_pos» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_and_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_or_pos» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_or_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_implies_pos» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_implies_neg1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_implies_neg2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_equiv_pos1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_equiv_pos2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_equiv_neg1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_equiv_neg2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_xor_pos1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_xor_pos2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_xor_neg1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_xor_neg2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_ite_pos1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_ite_pos2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_ite_pos3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_ite_neg1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_ite_neg2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cnf_ite_neg3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arrays_read_over_write» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arrays_read_over_write_contra» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arrays_read_over_write_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arrays_ext» =>
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
  case «cong» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «nary_cong» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «pairwise_cong» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «true_intro» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «true_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «false_intro» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «false_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ho_cong» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «distinct_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «distinct_true» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «distinct_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_sum_ub» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mult_pos» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mult_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_trichotomy» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «int_tight_ub» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «int_tight_lb» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mult_tangent» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mult_sign» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mult_abs_comparison» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_reduction» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_poly_norm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_poly_norm_rel» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_repeat_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_smulo_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_umulo_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_bitwise_slicing» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_bitblast_step» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_poly_norm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_poly_norm_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_length_pos» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_length_non_empty» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «concat_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «concat_unify» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «concat_csplit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «concat_split» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «concat_lprop» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «concat_cprop» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_decompose» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «exists_string_length» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_code_inj» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_seq_unit_inj» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_inter» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_unfold_pos» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_unfold_neg_concat_fixed» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_unfold_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_ext» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_reduction» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «string_eager_reduction» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_string_pred_entail» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_string_pred_safe_approx» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_eval» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_consume» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_loop_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_eq_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_inter_inclusion» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_union_inclusion» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_concat_star_char» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_sigma» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_sigma_star» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_ctn_multiset_subset» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_overlap_split_ctn» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_overlap_endpoints_ctn» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_overlap_endpoints_indexof» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_overlap_endpoints_replace» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_re_eval» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_re_eval» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_re_all_eval» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_eval_op» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_singleton_inj» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_ext» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_choose_member» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_eval_op» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ubv_to_int_range» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ubv_to_int_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «int_to_bv_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «instantiate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «skolemize» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «skolem_intro» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «alpha_equiv» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «beta_reduce» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_var_reordering» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «exists_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_unused_vars» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_merge_prenex» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_miniscope_and» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_miniscope_or» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_miniscope_ite» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_var_elim_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «quant_dt_split» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_split» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_inst» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_collapse_selector» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_collapse_tester» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_collapse_tester_singleton» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_cons_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_cons_eq_clash» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_cycle» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_collapse_updater» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «dt_updater_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_div_total_zero_real» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_div_total_zero_int» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_div_total» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_div_total_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_div_total_zero» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_div_total_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_mod_total» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_mod_total_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_mod_total_zero» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_mod_total_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_div_total_over_mod» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_elim_gt» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_elim_lt» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_elim_int_gt» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_elim_int_lt» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_elim_leq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_leq_norm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_geq_tighten» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_geq_norm1_int» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_geq_norm1_real» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_eq_elim_real» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_eq_elim_int» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_to_int_elim_to_real» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_is_int_elim_to_real» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_div_int_to_real» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_div_total_int_to_real» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mod_over_mod_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mod_over_mod» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_mod_over_mod_mult» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_eq_conflict» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_int_geq_tighten» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_divisible_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_abs_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_abs_int_gt» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_abs_real_gt» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_geq_ite_lift» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_leq_ite_lift» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_min_lt1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_min_lt2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_max_geq1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «arith_max_geq2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «array_read_over_write» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «array_read_over_write2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «array_store_overwrite» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «array_store_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «array_read_over_write_split» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «array_store_swap» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_double_not_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_not_true» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_not_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_eq_true» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_eq_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_eq_nrefl» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_impl_false1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_impl_false2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_impl_true1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_impl_true2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_impl_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_dual_impl_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_and_conf» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_and_conf2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_or_taut» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_or_taut2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_or_de_morgan» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_implies_de_morgan» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_and_de_morgan» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_or_and_distrib» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_implies_or_distrib» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_xor_refl» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_xor_nrefl» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_xor_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_xor_true» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_xor_comm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_xor_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_not_xor_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_not_eq_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_not_eq_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_neg_branch» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_then_true» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_else_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_then_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_else_true» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_then_lookahead_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_else_lookahead_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_then_lookahead_not_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_else_lookahead_not_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_expand» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bool_not_ite_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_true_cond» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_false_cond» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_not_cond» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_eq_branch» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_then_lookahead» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_else_lookahead» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_then_neg_lookahead» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ite_else_neg_lookahead» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_concat_extract_merge» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_extract» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_whole» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_concat_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_concat_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_concat_3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_concat_4» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_eq_extract_elim1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_eq_extract_elim2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_eq_extract_elim3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_not» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_sign_extend_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_sign_extend_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_sign_extend_3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_not_xor» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_and_simplify_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_and_simplify_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_or_simplify_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_or_simplify_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_simplify_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_simplify_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_simplify_3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ult_add_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_mult_slt_mult_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_mult_slt_mult_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_commutative_xor» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_commutative_comp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_zero_extend_eliminate_0» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sign_extend_eliminate_0» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_not_neq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ult_ones» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_concat_merge_const» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_commutative_add» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sub_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_width_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_width_one_not» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_eq_xor_solve» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_eq_not_solve» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ugt_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_uge_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sgt_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sge_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sle_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_redor_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_redand_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ule_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_comp_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_rotate_left_eliminate_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_rotate_left_eliminate_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_rotate_right_eliminate_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_rotate_right_eliminate_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_nand_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_nor_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xnor_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sdiv_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_zero_extend_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_uaddo_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_saddo_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sdivo_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_smod_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_srem_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_usubo_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ssubo_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_nego_eliminate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_equal_children» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_const_cond_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_const_cond_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_const_children_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_const_children_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_equal_cond_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_equal_cond_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_equal_cond_3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_merge_then_if» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_merge_else_if» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_merge_then_else» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ite_merge_else_else» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_shl_by_const_0» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_shl_by_const_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_shl_by_const_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_lshr_by_const_0» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_lshr_by_const_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_lshr_by_const_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ashr_by_const_0» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ashr_by_const_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ashr_by_const_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_and_concat_pullup» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_or_concat_pullup» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_concat_pullup» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_and_concat_pullup2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_or_concat_pullup2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_concat_pullup2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_and_concat_pullup3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_or_concat_pullup3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_concat_pullup3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_duplicate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_ones» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_xor_not» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_not_idemp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ult_zero_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ult_zero_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ult_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_lt_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ule_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ule_zero» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_zero_ule» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sle_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ule_max» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_not_ult» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_mult_pow2_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_mult_pow2_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_mult_pow2_2b» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_extract_mult_leading_bit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_udiv_pow2_not_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_udiv_zero» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_udiv_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_urem_pow2_not_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_urem_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_urem_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_shl_zero» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_lshr_zero» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ashr_zero» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ugt_urem» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_ult_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_merge_sign_extend_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_merge_sign_extend_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sign_extend_eq_const_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sign_extend_eq_const_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_zero_extend_eq_const_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_zero_extend_eq_const_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_zero_extend_ult_const_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_zero_extend_ult_const_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sign_extend_ult_const_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sign_extend_ult_const_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sign_extend_ult_const_3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bv_sign_extend_ult_const_4» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_eq_singleton_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_member_singleton» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_member_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_subset_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_insert_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_union_comm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_inter_comm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_inter_emp1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_inter_emp2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_minus_emp1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_minus_emp2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_union_emp1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_union_emp2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_inter_member» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_minus_member» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_union_member» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_choose_singleton» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_minus_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_union_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_inter_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_is_empty_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sets_is_singleton_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_ctn_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_ctn_full_false1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_ctn_full_false2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_len_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_empty_str» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_empty_range» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_empty_start» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_empty_start_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_substr_start_geq_len» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_eq_empty» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_z_eq_empty_leq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_eq_empty_leq_len» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len_replace_inv» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len_replace_all_inv» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len_update_inv» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_update_oob» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_update_rev» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_update_fit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_update_concat_fit0» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_update_concat_fit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_update_in_first_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len_substr_in_range» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_clash» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_clash_rev» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_clash2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_clash2_rev» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_unify» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_unify_rev» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_unify_base» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat_unify_base_rev» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_prefixof_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_suffixof_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_prefixof_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_suffixof_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_prefixof_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_suffixof_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_combine1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_combine2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_combine3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_combine4» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_concat1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_concat2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_replace» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_full» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_full_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_refl» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_concat_find» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_concat_find_contra» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_split_char» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_leq_len_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_char» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_at_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_id» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_prefix» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_prefix_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_no_contains» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_find_base» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_find_first_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_empty» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_one_pre» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_find_pre» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_all_no_contains» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_all_find_pre» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_all_find» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_all_empty» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_all_id» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_all_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_re_none» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_re_all_none» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len_concat_rec» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len_eq_zero_concat_rec» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len_eq_zero_base» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_no_contains» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_oob» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_oob2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_contains_pre» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_contains_concat_pre» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_prefix_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_len_oob» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_len_oob2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_find_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_eq_irr» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_re_none» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_re_emp_re» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_lower_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_upper_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_lower_upper» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_lower_idem» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_upper_lower» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_upper_idem» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_lower_len» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_upper_len» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_lower_from_int» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_upper_from_int» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_int_concat_neg_one» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_is_digit_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_leq_empty» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_leq_empty_eq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_leq_concat_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_leq_concat_true» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_leq_concat_base_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_leq_concat_base_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_lt_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_from_int_no_ctn_nondigit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_ctn_contra» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_ctn» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_dual_ctn» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_dual_ctn_false» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_self_ctn_simp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_emp_ctn_src» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_char_start_eq_len» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_repl_char» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_repl_self_tgt_char» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_repl_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains_repl_tgt» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_len_id» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_src_tgt_no_ctn» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_tgt_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_tgt_no_ctn» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_src_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_src_inv_no_ctn1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_src_inv_no_ctn2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_src_inv_no_ctn3» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_dual_self» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_dual_ite1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_dual_ite2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_repl_repl_lookahead_id_simp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_all_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_opt_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_diff_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_plus_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_repeat_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_concat_star_swap» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_concat_star_repeat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_concat_star_nullable1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_concat_star_nullable2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_concat_merge» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_union_all» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_union_const_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_inter_all» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_star_none» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_star_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_star_star» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_range_refl» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_range_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_range_non_singleton_1» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_range_non_singleton_2» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_star_union_char» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_star_union_drop_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_loop_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_loop_star» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_inter_cstring» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_inter_cstring_neg» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_len_include» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_len_include_pre» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr_len_norm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_len_rev» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_rev_rev» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_rev_concat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_repl_self_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_repl_no_change» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_repl_tgt_eq_len» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_repl_len_one_emp_prefix» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_repl_emp_tgt_nemp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_repl_nemp_src_emp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_eq_repl_self_src» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_len_unit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_nth_unit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_nth_concat_unit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_nth_concat_unit_gen» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_rev_unit» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_in_empty» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_in_sigma» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_in_sigma_star» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_in_cstring» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_in_comp» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_union_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_inter_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_range_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_contains» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_from_int_nemp_dig_range» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re_from_int_dig_range» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «eq_refl» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «eq_symm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «eq_cond_deq» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «eq_ite_lift» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «distinct_binary_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_bv2nat_int2bv» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_bv2nat_int2bv_extend» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_bv2nat_int2bv_extract» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_int2bv_bv2nat» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_bv2nat_geq_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_int2bv_bvult_equiv» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_int2bv_bvule_equiv» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uf_sbv_to_int_elim» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «evaluate» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «distinct_values» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «aci_norm» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «absorb» =>
    simp only [enc_CRule, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «distinct_card_conflict» =>
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
/-- The tree of the store that a `SmtBindings` is stored as. -/
def enc_SmtBindings : Smtm.SmtBindings → Tree
  | Smtm.SmtBindings.nil => Tree.node schema.Constructor.eo__24emb_5fsbd_2enil []
  | Smtm.SmtBindings.cons x0 x1 x2 x3 => Tree.node schema.Constructor.eo__24emb_5fsbd_2econs [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2), (enc_SmtBindings x3)]
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
  | Smtm.SmtTerm.ite x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2eite [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.not x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2enot [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.or x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eor [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.and x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eand [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.imp x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d_3e [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.xor x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2exor [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.eq x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.lam x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2elam [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.bind x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebind [(enc_SmtBindings x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm._at_purify x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_40purify [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.plus x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_2b [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.neg x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_2d [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.mult x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_2a [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.lt x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.leq x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c_3d [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.gt x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.geq x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e_3d [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.to_real x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5freal [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.to_int x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5fint [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.is_int x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eis_5fint [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.abs x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eabs [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.uneg x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2euneg [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.div x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ediv [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.mod x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2emod [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.divisible x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2edivisible [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.int_pow2 x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2epow2 [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.int_log2 x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2elog2 [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.div_total x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.mod_total x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2emod_5ftotal [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.select x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eselect [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.store x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estore [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.map_diff x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2emap_5fdiff [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.concat x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2econcat [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.extract x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2eextract [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.repeat x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2erepeat [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvnot x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnot [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.bvand x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvand [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvor x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvor [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvnand x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnand [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvnor x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnor [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvxor x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxor [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvxnor x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxnor [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvcomp x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvcomp [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvneg x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvneg [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.bvadd x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvadd [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvmul x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvmul [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvudiv x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvudiv [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvurem x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvurem [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsub x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsub [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsdiv x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdiv [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsrem x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsrem [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsmod x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmod [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvult x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvult [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvule x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvule [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvugt x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvugt [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvuge x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuge [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvslt x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvslt [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsle x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsle [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsgt x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsgt [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsge x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsge [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvshl x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvshl [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvlshr x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvlshr [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvashr x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvashr [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.zero_extend x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ezero_5fextend [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.sign_extend x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2esign_5fextend [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.rotate_left x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fleft [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.rotate_right x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fright [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvuaddo x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuaddo [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvnego x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnego [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.bvsaddo x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsaddo [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvumulo x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvumulo [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsmulo x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmulo [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvusubo x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvusubo [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvssubo x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvssubo [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.bvsdivo x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdivo [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.seq_empty x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eempty [(enc_SmtType x0)]
  | Smtm.SmtTerm.str_len x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2elen [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_concat x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_substr x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esubstr [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_contains x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2econtains [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_replace x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_indexof x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_at x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eat [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_prefixof x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_suffixof x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_rev x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2erev [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_update x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eupdate [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_to_lower x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_to_upper x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_to_code x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_from_code x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_is_digit x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_to_int x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_from_int x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.str_lt x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_leq x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_replace_all x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_replace_re x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_replace_re_all x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_indexof_re x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.re_allchar => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eallchar []
  | Smtm.SmtTerm.re_none => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2enone []
  | Smtm.SmtTerm.re_all => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eall []
  | Smtm.SmtTerm.str_to_re x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.re_mult x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2a [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.re_plus x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.re_exp x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_5e [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.re_opt x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eopt [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.re_comp x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ecomp [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.re_range x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2erange [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.re_concat x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.re_inter x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2einter [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.re_union x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eunion [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.re_diff x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ediff [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.re_loop x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eloop [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.str_in_re x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.seq_unit x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eunit [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.seq_nth x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2enth [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.str_indexof_re_split x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.seq_diff x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm._at_strings_occur_index x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.choice x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2echoice [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.set_empty x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eempty [(enc_SmtType x0)]
  | Smtm.SmtTerm.set_singleton x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esingleton [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.set_union x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eunion [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.set_inter x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2einter [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.set_minus x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eminus [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.set_member x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2emember [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.set_subset x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esubset [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.qdiv x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.qdiv_total x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.forall x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2eforall [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.exists x0 x1 x2 => Tree.node schema.Constructor.eo__24emb_5fsm_2eexists [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)]
  | Smtm.SmtTerm.int_to_bv x0 x1 => Tree.node schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv [(enc_SmtTerm x0), (enc_SmtTerm x1)]
  | Smtm.SmtTerm.ubv_to_int x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint [(enc_SmtTerm x0)]
  | Smtm.SmtTerm.sbv_to_int x0 => Tree.node schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint [(enc_SmtTerm x0)]
end

mutual
/-- The `SmtBindings` that a tree stands for. -/
def dec_SmtBindings : Tree → Option Smtm.SmtBindings
  | Tree.node schema.Constructor.eo__24emb_5fsbd_2enil [] => some Smtm.SmtBindings.nil
  | Tree.node schema.Constructor.eo__24emb_5fsbd_2econs [t0, t1, t2, t3] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtType t1
    let x2 ← dec_SmtTerm t2
    let x3 ← dec_SmtBindings t3
    some (Smtm.SmtBindings.cons x0 x1 x2 x3)
  | _ => none
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
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eite [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.ite x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2enot [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.not x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eor [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.or x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eand [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.and x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d_3e [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.imp x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2exor [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.xor x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.eq x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2elam [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtType t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.lam x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebind [t0, t1] => do
    let x0 ← dec_SmtBindings t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bind x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_40purify [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm._at_purify x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_2b [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.plus x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_2d [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.neg x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_2a [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.mult x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.lt x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c_3d [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.leq x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.gt x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e_3d [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.geq x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5freal [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.to_real x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5fint [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.to_int x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eis_5fint [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.is_int x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eabs [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.abs x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2euneg [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.uneg x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ediv [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.div x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2emod [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.mod x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2edivisible [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.divisible x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2epow2 [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.int_pow2 x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2elog2 [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.int_log2 x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.div_total x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2emod_5ftotal [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.mod_total x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eselect [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.select x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estore [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.store x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2emap_5fdiff [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.map_diff x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2econcat [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.concat x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eextract [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.extract x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2erepeat [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.repeat x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnot [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.bvnot x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvand [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvand x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvor [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvor x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnand [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvnand x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnor [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvnor x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxor [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvxor x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxnor [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvxnor x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvcomp [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvcomp x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvneg [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.bvneg x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvadd [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvadd x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvmul [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvmul x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvudiv [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvudiv x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvurem [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvurem x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsub [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsub x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdiv [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsdiv x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsrem [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsrem x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmod [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsmod x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvult [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvult x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvule [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvule x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvugt [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvugt x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuge [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvuge x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvslt [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvslt x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsle [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsle x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsgt [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsgt x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsge [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsge x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvshl [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvshl x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvlshr [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvlshr x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvashr [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvashr x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ezero_5fextend [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.zero_extend x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2esign_5fextend [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.sign_extend x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fleft [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.rotate_left x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fright [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.rotate_right x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuaddo [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvuaddo x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnego [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.bvnego x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsaddo [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsaddo x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvumulo [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvumulo x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmulo [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsmulo x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvusubo [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvusubo x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvssubo [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvssubo x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdivo [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.bvsdivo x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eempty [t0] => do
    let x0 ← dec_SmtType t0
    some (Smtm.SmtTerm.seq_empty x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2elen [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_len x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_concat x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esubstr [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_substr x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2econtains [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_contains x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_replace x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_indexof x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eat [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_at x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_prefixof x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_suffixof x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2erev [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_rev x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eupdate [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_update x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_to_lower x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_to_upper x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_to_code x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_from_code x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_is_digit x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_to_int x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_from_int x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_lt x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_leq x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_replace_all x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_replace_re x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_replace_re_all x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_indexof_re x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eallchar [] => some Smtm.SmtTerm.re_allchar
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2enone [] => some Smtm.SmtTerm.re_none
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eall [] => some Smtm.SmtTerm.re_all
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.str_to_re x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2a [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.re_mult x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.re_plus x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_5e [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.re_exp x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eopt [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.re_opt x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ecomp [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.re_comp x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2erange [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.re_range x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.re_concat x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2einter [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.re_inter x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eunion [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.re_union x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ediff [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.re_diff x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eloop [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.re_loop x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.str_in_re x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eunit [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.seq_unit x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2enth [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.seq_nth x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.str_indexof_re_split x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.seq_diff x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm._at_strings_occur_index x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre [t0, t1, t2] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2echoice [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtType t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.choice x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eempty [t0] => do
    let x0 ← dec_SmtType t0
    some (Smtm.SmtTerm.set_empty x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esingleton [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.set_singleton x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eunion [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.set_union x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2einter [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.set_inter x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eminus [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.set_minus x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2emember [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.set_member x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esubset [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.set_subset x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.qdiv x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.qdiv_total x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eforall [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtType t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.forall x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eexists [t0, t1, t2] => do
    let x0 ← Tree.decStr t0
    let x1 ← dec_SmtType t1
    let x2 ← dec_SmtTerm t2
    some (Smtm.SmtTerm.exists x0 x1 x2)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv [t0, t1] => do
    let x0 ← dec_SmtTerm t0
    let x1 ← dec_SmtTerm t1
    some (Smtm.SmtTerm.int_to_bv x0 x1)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.ubv_to_int x0)
  | Tree.node schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint [t0] => do
    let x0 ← dec_SmtTerm t0
    some (Smtm.SmtTerm.sbv_to_int x0)
  | _ => none
end

mutual
/-- A `SmtBindings` that the store can hold: its natives fit the runtime's. -/
def emb_SmtBindings : Smtm.SmtBindings → Prop
  | Smtm.SmtBindings.nil => True
  | Smtm.SmtBindings.cons x0 x1 x2 x3 => Tree.okStr x0 ∧ emb_SmtType x1 ∧ emb_SmtTerm x2 ∧ emb_SmtBindings x3
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
  | Smtm.SmtTerm.ite x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.not x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.or x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.and x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.imp x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.xor x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.eq x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.lam x0 x1 x2 => Tree.okStr x0 ∧ emb_SmtType x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.bind x0 x1 => emb_SmtBindings x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm._at_purify x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.plus x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.neg x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.mult x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.lt x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.leq x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.gt x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.geq x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.to_real x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.to_int x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.is_int x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.abs x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.uneg x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.div x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.mod x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.divisible x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.int_pow2 x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.int_log2 x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.div_total x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.mod_total x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.select x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.store x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.map_diff x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.concat x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.extract x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.repeat x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvnot x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.bvand x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvor x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvnand x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvnor x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvxor x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvxnor x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvcomp x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvneg x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.bvadd x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvmul x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvudiv x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvurem x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsub x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsdiv x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsrem x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsmod x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvult x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvule x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvugt x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvuge x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvslt x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsle x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsgt x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsge x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvshl x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvlshr x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvashr x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.zero_extend x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.sign_extend x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.rotate_left x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.rotate_right x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvuaddo x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvnego x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.bvsaddo x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvumulo x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsmulo x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvusubo x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvssubo x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.bvsdivo x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.seq_empty x0 => emb_SmtType x0
  | Smtm.SmtTerm.str_len x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_concat x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_substr x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_contains x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_replace x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_indexof x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_at x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_prefixof x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_suffixof x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_rev x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_update x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_to_lower x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_to_upper x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_to_code x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_from_code x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_is_digit x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_to_int x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_from_int x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.str_lt x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_leq x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_replace_all x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_replace_re x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_replace_re_all x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_indexof_re x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.re_allchar => True
  | Smtm.SmtTerm.re_none => True
  | Smtm.SmtTerm.re_all => True
  | Smtm.SmtTerm.str_to_re x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.re_mult x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.re_plus x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.re_exp x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.re_opt x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.re_comp x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.re_range x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.re_concat x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.re_inter x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.re_union x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.re_diff x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.re_loop x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.str_in_re x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.seq_unit x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.seq_nth x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.str_indexof_re_split x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.seq_diff x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm._at_strings_occur_index x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2 => emb_SmtTerm x0 ∧ emb_SmtTerm x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.choice x0 x1 x2 => Tree.okStr x0 ∧ emb_SmtType x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.set_empty x0 => emb_SmtType x0
  | Smtm.SmtTerm.set_singleton x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.set_union x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.set_inter x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.set_minus x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.set_member x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.set_subset x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.qdiv x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.qdiv_total x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.forall x0 x1 x2 => Tree.okStr x0 ∧ emb_SmtType x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.exists x0 x1 x2 => Tree.okStr x0 ∧ emb_SmtType x1 ∧ emb_SmtTerm x2
  | Smtm.SmtTerm.int_to_bv x0 x1 => emb_SmtTerm x0 ∧ emb_SmtTerm x1
  | Smtm.SmtTerm.ubv_to_int x0 => emb_SmtTerm x0
  | Smtm.SmtTerm.sbv_to_int x0 => emb_SmtTerm x0
end

mutual
theorem dec_enc_SmtBindings : (x : Smtm.SmtBindings) → emb_SmtBindings x → dec_SmtBindings (enc_SmtBindings x) = some x
  | Smtm.SmtBindings.nil, h => by
    simp only [enc_SmtBindings]
    unfold dec_SmtBindings
    rfl
  | Smtm.SmtBindings.cons x0 x1 x2 x3, h => by
    simp only [emb_SmtBindings] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp only [enc_SmtBindings]
    unfold dec_SmtBindings
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2, dec_enc_SmtBindings x3 h3, Option.bind_some]
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
  | Smtm.SmtTerm.ite x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.not x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.or x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.and x0 x1, h => by
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
  | Smtm.SmtTerm.xor x0 x1, h => by
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
  | Smtm.SmtTerm.lam x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.bind x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtBindings x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm._at_purify x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.plus x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.neg x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.mult x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.lt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.leq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.gt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.geq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.to_real x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.is_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.abs x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.uneg x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.div x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.mod x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.divisible x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.int_pow2 x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.int_log2 x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.div_total x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.mod_total x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.select x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.store x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.map_diff x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.concat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.extract x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.repeat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvnot x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.bvand x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvnand x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvnor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvxor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvxnor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvcomp x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvneg x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.bvadd x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvmul x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvudiv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvurem x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsub x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsdiv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsrem x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsmod x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvult x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvule x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvugt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvuge x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvslt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsle x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsgt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsge x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvshl x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvlshr x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvashr x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.zero_extend x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.sign_extend x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.rotate_left x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.rotate_right x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvuaddo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvnego x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.bvsaddo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvumulo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsmulo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvusubo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvssubo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.bvsdivo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.seq_empty x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_len x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_concat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_substr x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_contains x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_replace x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_indexof x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_at x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_prefixof x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_suffixof x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_rev x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_update x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_to_lower x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_to_upper x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_to_code x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_from_code x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_is_digit x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_from_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.str_lt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_leq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_replace_all x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_replace_re x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_replace_re_all x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_indexof_re x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.re_allchar, h => by
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    rfl
  | Smtm.SmtTerm.re_none, h => by
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    rfl
  | Smtm.SmtTerm.re_all, h => by
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    rfl
  | Smtm.SmtTerm.str_to_re x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.re_mult x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.re_plus x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.re_exp x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.re_opt x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.re_comp x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.re_range x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.re_concat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.re_inter x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.re_union x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.re_diff x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.re_loop x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.str_in_re x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.seq_unit x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.seq_nth x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.str_indexof_re_split x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.seq_diff x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm._at_strings_occur_index x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.choice x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.set_empty x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtType x0 h0, Option.bind_some]
  | Smtm.SmtTerm.set_singleton x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.set_union x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.set_inter x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.set_minus x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.set_member x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.set_subset x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.qdiv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.qdiv_total x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.forall x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.exists x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2, Option.bind_some]
  | Smtm.SmtTerm.int_to_bv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, Option.bind_some]
  | Smtm.SmtTerm.ubv_to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
  | Smtm.SmtTerm.sbv_to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp only [enc_SmtTerm]
    unfold dec_SmtTerm
    simp only [Option.bind_eq_bind, dec_enc_SmtTerm x0 h0, Option.bind_some]
end

theorem inv_SmtBindings_nil {x : Smtm.SmtBindings} {ts : List Tree}
    (h : enc_SmtBindings x = Tree.node schema.Constructor.eo__24emb_5fsbd_2enil ts) (he : emb_SmtBindings x) :
    x = Smtm.SmtBindings.nil ∧ ts = [] := by
  have hd := dec_enc_SmtBindings x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtBindings at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtBindings at hd
    cases hd

theorem inv_SmtBindings_cons {x : Smtm.SmtBindings} {ts : List Tree}
    (h : enc_SmtBindings x = Tree.node schema.Constructor.eo__24emb_5fsbd_2econs ts) (he : emb_SmtBindings x) :
    ∃ x0 x1 x2 x3, x = Smtm.SmtBindings.cons x0 x1 x2 x3 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2), (enc_SmtBindings x3)] := by
  have hd := dec_enc_SmtBindings x he
  rw [h] at hd
  rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨_, _⟩⟩⟩⟩⟩
  · unfold dec_SmtBindings at hd
    cases hd
  · unfold dec_SmtBindings at hd
    cases hd
  · unfold dec_SmtBindings at hd
    cases hd
  · unfold dec_SmtBindings at hd
    cases hd
  · unfold dec_SmtBindings at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hd
    obtain ⟨x0, -, x1, -, x2, -, x3, -, rfl⟩ := hd
    simp only [enc_SmtBindings, Tree.node.injEq, true_and] at h
    exact ⟨_, _, _, _, rfl, h.symm⟩
  · unfold dec_SmtBindings at hd
    cases hd

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

theorem inv_SmtTerm_xor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2exor ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.xor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_lam {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2elam ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.lam x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_bind {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebind ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bind x0 x1 ∧ ts = [(enc_SmtBindings x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm__at_purify {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_40purify ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm._at_purify x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_plus {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2b ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.plus x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_neg {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2d ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.neg x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_mult {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2a ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.mult x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_lt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.lt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_leq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c_3d ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.leq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_gt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.gt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_geq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e_3d ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.geq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_to_real {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5freal ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.to_real x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5fint ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_is_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eis_5fint ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.is_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_abs {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eabs ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.abs x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_uneg {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2euneg ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.uneg x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_div {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ediv ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.div x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_mod {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2emod ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.mod x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_divisible {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2edivisible ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.divisible x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_int_pow2 {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2epow2 ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.int_pow2 x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_int_log2 {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2elog2 ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.int_log2 x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_div_total {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.div_total x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_mod_total {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2emod_5ftotal ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.mod_total x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_select {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eselect ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.select x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_store {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estore ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.store x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_map_diff {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2emap_5fdiff ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.map_diff x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_concat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2econcat ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.concat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_extract {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eextract ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.extract x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_repeat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2erepeat ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.repeat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvnot {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnot ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.bvnot x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_bvand {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvand ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvand x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvor ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvnand {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnand ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvnand x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvnor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnor ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvnor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvxor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxor ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvxor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvxnor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxnor ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvxnor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvcomp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvcomp ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvcomp x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvneg {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvneg ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.bvneg x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_bvadd {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvadd ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvadd x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvmul {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvmul ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvmul x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvudiv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvudiv ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvudiv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvurem {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvurem ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvurem x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsub {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsub ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsub x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsdiv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdiv ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsdiv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsrem {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsrem ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsrem x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsmod {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmod ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsmod x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvult {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvult ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvult x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvule {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvule ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvule x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvugt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvugt ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvugt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvuge {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuge ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvuge x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvslt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvslt ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvslt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsle {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsle ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsle x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsgt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsgt ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsgt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsge {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsge ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsge x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvshl {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvshl ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvshl x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvlshr {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvlshr ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvlshr x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvashr {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvashr ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvashr x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_zero_extend {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ezero_5fextend ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.zero_extend x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_sign_extend {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2esign_5fextend ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.sign_extend x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_rotate_left {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fleft ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.rotate_left x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_rotate_right {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fright ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.rotate_right x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvuaddo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuaddo ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvuaddo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvnego {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnego ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.bvnego x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_bvsaddo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsaddo ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsaddo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvumulo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvumulo ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvumulo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsmulo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmulo ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsmulo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvusubo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvusubo ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvusubo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvssubo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvssubo ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvssubo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_bvsdivo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdivo ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsdivo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_seq_empty {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eempty ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.seq_empty x0 ∧ ts = [(enc_SmtType x0)] := by
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

theorem inv_SmtTerm_str_len {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2elen ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_len x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_concat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_concat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_substr {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esubstr ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_substr x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_contains {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2econtains ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_contains x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_replace {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_indexof {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_indexof x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_at {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eat ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_at x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_prefixof {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_prefixof x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_suffixof {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_suffixof x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_rev {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2erev ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_rev x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_update {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eupdate ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_update x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_to_lower {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_to_lower x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_to_upper {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_to_upper x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_to_code {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_to_code x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_from_code {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_from_code x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_is_digit {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_is_digit x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_from_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_from_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_str_lt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_lt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_leq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_leq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_replace_all {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace_all x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_replace_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace_re x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_replace_re_all {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace_re_all x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_indexof_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_indexof_re x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_re_allchar {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eallchar ts) (he : emb_SmtTerm x) :
    x = Smtm.SmtTerm.re_allchar ∧ ts = [] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtTerm at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_re_none {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2enone ts) (he : emb_SmtTerm x) :
    x = Smtm.SmtTerm.re_none ∧ ts = [] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtTerm at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_re_all {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eall ts) (he : emb_SmtTerm x) :
    x = Smtm.SmtTerm.re_all ∧ ts = [] := by
  have hd := dec_enc_SmtTerm x he
  rw [h] at hd
  rcases ts with _ | ⟨_, _⟩
  · unfold dec_SmtTerm at hd
    cases hd
    exact ⟨rfl, rfl⟩
  · unfold dec_SmtTerm at hd
    cases hd

theorem inv_SmtTerm_str_to_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.str_to_re x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_re_mult {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2a ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.re_mult x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_re_plus {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.re_plus x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_re_exp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_5e ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_exp x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_re_opt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eopt ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.re_opt x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_re_comp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ecomp ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.re_comp x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_re_range {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2erange ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_range x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_re_concat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_concat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_re_inter {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2einter ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_inter x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_re_union {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eunion ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_union x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_re_diff {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ediff ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_diff x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_re_loop {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eloop ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.re_loop x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_str_in_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_in_re x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_seq_unit {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eunit ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.seq_unit x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_seq_nth {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2enth ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.seq_nth x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_str_indexof_re_split {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_indexof_re_split x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_seq_diff {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.seq_diff x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm__at_strings_occur_index {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm._at_strings_occur_index x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm__at_strings_occur_index_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_choice {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2echoice ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.choice x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_set_empty {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eempty ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.set_empty x0 ∧ ts = [(enc_SmtType x0)] := by
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

theorem inv_SmtTerm_set_singleton {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esingleton ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.set_singleton x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_set_union {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eunion ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_union x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_set_inter {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2einter ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_inter x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_set_minus {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eminus ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_minus x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_set_member {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2emember ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_member x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_set_subset {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esubset ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_subset x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_qdiv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.qdiv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_qdiv_total {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.qdiv_total x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_forall {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eforall ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.forall x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_exists {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eexists ts) (he : emb_SmtTerm x) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.exists x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
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

theorem inv_SmtTerm_int_to_bv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv ts) (he : emb_SmtTerm x) :
    ∃ x0 x1, x = Smtm.SmtTerm.int_to_bv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
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

theorem inv_SmtTerm_ubv_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.ubv_to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem inv_SmtTerm_sbv_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint ts) (he : emb_SmtTerm x) :
    ∃ x0, x = Smtm.SmtTerm.sbv_to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
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

theorem enc_SmtBindings_node {x : Smtm.SmtBindings} {c : schema.Constructor} {ts : List Tree}
    (h : enc_SmtBindings x = Tree.node c ts) :
    c.embedding = Result.ok Embedding.Data ∨ c.embedding = Result.ok Embedding.Var := by
  cases x
  case «nil» =>
    simp only [enc_SmtBindings, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «cons» =>
    simp only [enc_SmtBindings, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

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
  case «ite» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «not» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «or» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «and» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «imp» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «xor» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «eq» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «lam» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bind» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «_at_purify» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «plus» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «neg» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «mult» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «lt» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «leq» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «gt» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «geq» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «to_real» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «to_int» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «is_int» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «abs» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «uneg» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «div» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «mod» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «divisible» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «int_pow2» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «int_log2» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «div_total» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «mod_total» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «select» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «store» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «map_diff» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «concat» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «extract» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «repeat» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvnot» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvand» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvor» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvnand» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvnor» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvxor» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvxnor» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvcomp» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvneg» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvadd» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvmul» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvudiv» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvurem» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsub» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsdiv» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsrem» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsmod» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvult» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvule» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvugt» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvuge» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvslt» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsle» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsgt» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsge» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvshl» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvlshr» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvashr» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «zero_extend» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sign_extend» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «rotate_left» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «rotate_right» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvuaddo» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvnego» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsaddo» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvumulo» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsmulo» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvusubo» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvssubo» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «bvsdivo» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_empty» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_len» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_concat» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_substr» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_contains» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_at» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_prefixof» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_suffixof» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_rev» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_update» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_lower» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_upper» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_code» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_from_code» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_is_digit» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_int» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_from_int» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_lt» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_leq» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_all» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_re» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_replace_re_all» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_re» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_allchar» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_none» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_all» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_to_re» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_mult» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_plus» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_exp» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_opt» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_comp» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_range» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_concat» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_inter» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_union» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_diff» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «re_loop» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_in_re» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_unit» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_nth» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «str_indexof_re_split» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «seq_diff» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «_at_strings_occur_index» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «_at_strings_occur_index_re» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «choice» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «set_empty» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «set_singleton» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «set_union» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «set_inter» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «set_minus» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «set_member» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «set_subset» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «qdiv» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «qdiv_total» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «forall» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «exists» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «int_to_bv» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «ubv_to_int» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  case «sbv_to_int» =>
    simp only [enc_SmtTerm, Tree.node.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl

instance : Embedded Smtm.SmtBindings := ⟨enc_SmtBindings, dec_SmtBindings, emb_SmtBindings, dec_enc_SmtBindings⟩

@[simp] theorem embedded_enc_SmtBindings (x : Smtm.SmtBindings) : Embedded.enc x = enc_SmtBindings x := rfl
@[simp] theorem embedded_emb_SmtBindings (x : Smtm.SmtBindings) : Embedded.emb x = emb_SmtBindings x := rfl

instance : Embedded Smtm.SmtTerm := ⟨enc_SmtTerm, dec_SmtTerm, emb_SmtTerm, dec_enc_SmtTerm⟩

@[simp] theorem embedded_enc_SmtTerm (x : Smtm.SmtTerm) : Embedded.enc x = enc_SmtTerm x := rfl
@[simp] theorem embedded_emb_SmtTerm (x : Smtm.SmtTerm) : Embedded.emb x = emb_SmtTerm x := rfl


end

end pathos_compiled_checker.Embed
