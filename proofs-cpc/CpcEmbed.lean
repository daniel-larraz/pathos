module

public import CpcChecker
public import PathosProofs.Store.Tree
public import Cpc.Logos
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
- `CArgList`: the field Term of cons
- `CCmd`: the field Term of assume_push
- `CCmdList`: the field CCmd of cons
- `CState`: the field CStateObj of cons
- `CStateObj`: the field Term of assume
- `Datatype`: the field DatatypeCons of sum
- `DatatypeCons`: the field Term of cons
- `DatatypeDecl`: the field Datatype of cons
- `Proof`: the field Term of pf
- `SmtMap`: the field SmtValue of cons
- `SmtRegLan`: the field SmtValue of char
- `SmtSeq`: the field SmtValue of cons
- `SmtValue`: the field native_Real of Real
- `Term`: an indexed user operator
-/

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

theorem inv_CIndexList_nil {x : Eo.CIndexList} {ts : List Tree}
    (h : enc_CIndexList x = Tree.node schema.Constructor.eo__24emb_5findl_2enil ts) :
    x = Eo.CIndexList.nil ∧ ts = [] := by
  cases x <;> simp_all [enc_CIndexList]

theorem inv_CIndexList_cons {x : Eo.CIndexList} {ts : List Tree}
    (h : enc_CIndexList x = Tree.node schema.Constructor.eo__24emb_5findl_2econs ts) :
    ∃ x0 x1, x = Eo.CIndexList.cons x0 x1 ∧ ts = [(Tree.encInt x0), (enc_CIndexList x1)] := by
  cases x <;> simp_all [enc_CIndexList]

mutual
theorem dec_enc_CIndexList : (x : Eo.CIndexList) → emb_CIndexList x → dec_CIndexList (enc_CIndexList x) = some x
  | Eo.CIndexList.nil, h => by
    simp [enc_CIndexList, dec_CIndexList]
  | Eo.CIndexList.cons x0 x1, h => by
    simp only [emb_CIndexList] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_CIndexList, dec_CIndexList, Tree.dec_encInt x0 h0, dec_enc_CIndexList x1 h1]
end

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

theorem inv_CRule_scope {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2escope ts) :
    x = Eo.CRule.scope ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_process_scope {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eprocess_5fscope ts) :
    x = Eo.CRule.process_scope ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq ts) :
    x = Eo.CRule.ite_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esplit ts) :
    x = Eo.CRule.split ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_resolution {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eresolution ts) :
    x = Eo.CRule.resolution ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_chain_resolution {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fresolution ts) :
    x = Eo.CRule.chain_resolution ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_chain_m_resolution {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution ts) :
    x = Eo.CRule.chain_m_resolution ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_factoring {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2efactoring ts) :
    x = Eo.CRule.factoring ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_reordering {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ereordering ts) :
    x = Eo.CRule.reordering ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_eq_resolve {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fresolve ts) :
    x = Eo.CRule.eq_resolve ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_modus_ponens {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2emodus_5fponens ts) :
    x = Eo.CRule.modus_ponens ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_not_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim ts) :
    x = Eo.CRule.not_not_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econtra ts) :
    x = Eo.CRule.contra ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_and_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eand_5felim ts) :
    x = Eo.CRule.and_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_and_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eand_5fintro ts) :
    x = Eo.CRule.and_intro ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_or_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5for_5felim ts) :
    x = Eo.CRule.not_or_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_implies_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eimplies_5felim ts) :
    x = Eo.CRule.implies_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_implies_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 ts) :
    x = Eo.CRule.not_implies_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_implies_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 ts) :
    x = Eo.CRule.not_implies_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_equiv_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 ts) :
    x = Eo.CRule.equiv_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_equiv_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 ts) :
    x = Eo.CRule.equiv_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_equiv_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 ts) :
    x = Eo.CRule.not_equiv_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_equiv_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 ts) :
    x = Eo.CRule.not_equiv_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_xor_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim1 ts) :
    x = Eo.CRule.xor_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_xor_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2exor_5felim2 ts) :
    x = Eo.CRule.xor_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_xor_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 ts) :
    x = Eo.CRule.not_xor_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_xor_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 ts) :
    x = Eo.CRule.not_xor_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim1 ts) :
    x = Eo.CRule.ite_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felim2 ts) :
    x = Eo.CRule.ite_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_ite_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 ts) :
    x = Eo.CRule.not_ite_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_ite_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 ts) :
    x = Eo.CRule.not_ite_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_not_and {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enot_5fand ts) :
    x = Eo.CRule.not_and ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_and_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos ts) :
    x = Eo.CRule.cnf_and_pos ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_and_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg ts) :
    x = Eo.CRule.cnf_and_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_or_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos ts) :
    x = Eo.CRule.cnf_or_pos ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_or_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg ts) :
    x = Eo.CRule.cnf_or_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_implies_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos ts) :
    x = Eo.CRule.cnf_implies_pos ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_implies_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 ts) :
    x = Eo.CRule.cnf_implies_neg1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_implies_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 ts) :
    x = Eo.CRule.cnf_implies_neg2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_equiv_pos1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 ts) :
    x = Eo.CRule.cnf_equiv_pos1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_equiv_pos2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 ts) :
    x = Eo.CRule.cnf_equiv_pos2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_equiv_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 ts) :
    x = Eo.CRule.cnf_equiv_neg1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_equiv_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 ts) :
    x = Eo.CRule.cnf_equiv_neg2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_xor_pos1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 ts) :
    x = Eo.CRule.cnf_xor_pos1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_xor_pos2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 ts) :
    x = Eo.CRule.cnf_xor_pos2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_xor_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 ts) :
    x = Eo.CRule.cnf_xor_neg1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_xor_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 ts) :
    x = Eo.CRule.cnf_xor_neg2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_ite_pos1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 ts) :
    x = Eo.CRule.cnf_ite_pos1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_ite_pos2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 ts) :
    x = Eo.CRule.cnf_ite_pos2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_ite_pos3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 ts) :
    x = Eo.CRule.cnf_ite_pos3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_ite_neg1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 ts) :
    x = Eo.CRule.cnf_ite_neg1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_ite_neg2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 ts) :
    x = Eo.CRule.cnf_ite_neg2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cnf_ite_neg3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 ts) :
    x = Eo.CRule.cnf_ite_neg3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arrays_read_over_write {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite ts) :
    x = Eo.CRule.arrays_read_over_write ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arrays_read_over_write_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra ts) :
    x = Eo.CRule.arrays_read_over_write_contra ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arrays_read_over_write_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 ts) :
    x = Eo.CRule.arrays_read_over_write_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arrays_ext {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earrays_5fext ts) :
    x = Eo.CRule.arrays_ext ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2erefl ts) :
    x = Eo.CRule.refl ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_symm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esymm ts) :
    x = Eo.CRule.symm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_trans {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2etrans ts) :
    x = Eo.CRule.trans ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econg ts) :
    x = Eo.CRule.cong ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_nary_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2enary_5fcong ts) :
    x = Eo.CRule.nary_cong ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_pairwise_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2epairwise_5fcong ts) :
    x = Eo.CRule.pairwise_cong ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_true_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5fintro ts) :
    x = Eo.CRule.true_intro ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_true_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2etrue_5felim ts) :
    x = Eo.CRule.true_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_false_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5fintro ts) :
    x = Eo.CRule.false_intro ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_false_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2efalse_5felim ts) :
    x = Eo.CRule.false_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ho_cong {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eho_5fcong ts) :
    x = Eo.CRule.ho_cong ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_distinct_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5felim ts) :
    x = Eo.CRule.distinct_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_distinct_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue ts) :
    x = Eo.CRule.distinct_true ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_distinct_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse ts) :
    x = Eo.CRule.distinct_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_sum_ub {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub ts) :
    x = Eo.CRule.arith_sum_ub ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mult_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos ts) :
    x = Eo.CRule.arith_mult_pos ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mult_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg ts) :
    x = Eo.CRule.arith_mult_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_trichotomy {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy ts) :
    x = Eo.CRule.arith_trichotomy ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_int_tight_ub {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub ts) :
    x = Eo.CRule.int_tight_ub ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_int_tight_lb {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb ts) :
    x = Eo.CRule.int_tight_lb ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mult_tangent {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent ts) :
    x = Eo.CRule.arith_mult_tangent ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mult_sign {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign ts) :
    x = Eo.CRule.arith_mult_sign ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mult_abs_comparison {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison ts) :
    x = Eo.CRule.arith_mult_abs_comparison ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_reduction {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5freduction ts) :
    x = Eo.CRule.arith_reduction ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_poly_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm ts) :
    x = Eo.CRule.arith_poly_norm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_poly_norm_rel {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel ts) :
    x = Eo.CRule.arith_poly_norm_rel ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_repeat_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim ts) :
    x = Eo.CRule.bv_repeat_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_smulo_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim ts) :
    x = Eo.CRule.bv_smulo_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_umulo_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim ts) :
    x = Eo.CRule.bv_umulo_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_bitwise_slicing {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing ts) :
    x = Eo.CRule.bv_bitwise_slicing ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_bitblast_step {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep ts) :
    x = Eo.CRule.bv_bitblast_step ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_poly_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm ts) :
    x = Eo.CRule.bv_poly_norm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_poly_norm_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq ts) :
    x = Eo.CRule.bv_poly_norm_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_length_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos ts) :
    x = Eo.CRule.string_length_pos ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_length_non_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty ts) :
    x = Eo.CRule.string_length_non_empty ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_concat_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5feq ts) :
    x = Eo.CRule.concat_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_concat_unify {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5funify ts) :
    x = Eo.CRule.concat_unify ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_concat_csplit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit ts) :
    x = Eo.CRule.concat_csplit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_concat_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fsplit ts) :
    x = Eo.CRule.concat_split ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_concat_lprop {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5flprop ts) :
    x = Eo.CRule.concat_lprop ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_concat_cprop {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2econcat_5fcprop ts) :
    x = Eo.CRule.concat_cprop ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_decompose {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fdecompose ts) :
    x = Eo.CRule.string_decompose ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_exists_string_length {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength ts) :
    x = Eo.CRule.exists_string_length ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_code_inj {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj ts) :
    x = Eo.CRule.string_code_inj ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_seq_unit_inj {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj ts) :
    x = Eo.CRule.string_seq_unit_inj ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_inter {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter ts) :
    x = Eo.CRule.re_inter ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat ts) :
    x = Eo.CRule.re_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_unfold_pos {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos ts) :
    x = Eo.CRule.re_unfold_pos ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_unfold_neg_concat_fixed {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed ts) :
    x = Eo.CRule.re_unfold_neg_concat_fixed ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_unfold_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg ts) :
    x = Eo.CRule.re_unfold_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_ext {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5fext ts) :
    x = Eo.CRule.string_ext ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_reduction {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5freduction ts) :
    x = Eo.CRule.string_reduction ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_string_eager_reduction {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction ts) :
    x = Eo.CRule.string_eager_reduction ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_string_pred_entail {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail ts) :
    x = Eo.CRule.arith_string_pred_entail ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_string_pred_safe_approx {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox ts) :
    x = Eo.CRule.arith_string_pred_safe_approx ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval ts) :
    x = Eo.CRule.str_in_re_eval ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_consume {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume ts) :
    x = Eo.CRule.str_in_re_consume ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_loop_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim ts) :
    x = Eo.CRule.re_loop_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_eq_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim ts) :
    x = Eo.CRule.re_eq_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_inter_inclusion {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion ts) :
    x = Eo.CRule.re_inter_inclusion ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_union_inclusion {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion ts) :
    x = Eo.CRule.re_union_inclusion ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_concat_star_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar ts) :
    x = Eo.CRule.str_in_re_concat_star_char ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_sigma {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma ts) :
    x = Eo.CRule.str_in_re_sigma ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_sigma_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar ts) :
    x = Eo.CRule.str_in_re_sigma_star ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_ctn_multiset_subset {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset ts) :
    x = Eo.CRule.str_ctn_multiset_subset ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_overlap_split_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn ts) :
    x = Eo.CRule.str_overlap_split_ctn ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_overlap_endpoints_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn ts) :
    x = Eo.CRule.str_overlap_endpoints_ctn ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_overlap_endpoints_indexof {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof ts) :
    x = Eo.CRule.str_overlap_endpoints_indexof ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_overlap_endpoints_replace {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace ts) :
    x = Eo.CRule.str_overlap_endpoints_replace ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_re_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval ts) :
    x = Eo.CRule.str_indexof_re_eval ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_re_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval ts) :
    x = Eo.CRule.str_replace_re_eval ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_re_all_eval {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval ts) :
    x = Eo.CRule.str_replace_re_all_eval ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_eval_op {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop ts) :
    x = Eo.CRule.seq_eval_op ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_singleton_inj {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj ts) :
    x = Eo.CRule.sets_singleton_inj ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_ext {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fext ts) :
    x = Eo.CRule.sets_ext ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_choose_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember ts) :
    x = Eo.CRule.sets_choose_member ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_eval_op {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop ts) :
    x = Eo.CRule.sets_eval_op ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ubv_to_int_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange ts) :
    x = Eo.CRule.ubv_to_int_range ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ubv_to_int_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim ts) :
    x = Eo.CRule.ubv_to_int_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_int_to_bv_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim ts) :
    x = Eo.CRule.int_to_bv_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_instantiate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2einstantiate ts) :
    x = Eo.CRule.instantiate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_skolemize {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eskolemize ts) :
    x = Eo.CRule.skolemize ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_skolem_intro {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eskolem_5fintro ts) :
    x = Eo.CRule.skolem_intro ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_alpha_equiv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv ts) :
    x = Eo.CRule.alpha_equiv ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_beta_reduce {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebeta_5freduce ts) :
    x = Eo.CRule.beta_reduce ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_var_reordering {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering ts) :
    x = Eo.CRule.quant_var_reordering ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_exists_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eexists_5felim ts) :
    x = Eo.CRule.exists_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_unused_vars {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars ts) :
    x = Eo.CRule.quant_unused_vars ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_merge_prenex {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex ts) :
    x = Eo.CRule.quant_merge_prenex ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_miniscope_and {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand ts) :
    x = Eo.CRule.quant_miniscope_and ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_miniscope_or {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for ts) :
    x = Eo.CRule.quant_miniscope_or ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_miniscope_ite {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite ts) :
    x = Eo.CRule.quant_miniscope_ite ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_var_elim_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq ts) :
    x = Eo.CRule.quant_var_elim_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_quant_dt_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit ts) :
    x = Eo.CRule.quant_dt_split ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fsplit ts) :
    x = Eo.CRule.dt_split ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_inst {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5finst ts) :
    x = Eo.CRule.dt_inst ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_collapse_selector {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector ts) :
    x = Eo.CRule.dt_collapse_selector ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_collapse_tester {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester ts) :
    x = Eo.CRule.dt_collapse_tester ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_collapse_tester_singleton {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton ts) :
    x = Eo.CRule.dt_collapse_tester_singleton ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_cons_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq ts) :
    x = Eo.CRule.dt_cons_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_cons_eq_clash {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash ts) :
    x = Eo.CRule.dt_cons_eq_clash ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_cycle {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcycle ts) :
    x = Eo.CRule.dt_cycle ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_collapse_updater {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater ts) :
    x = Eo.CRule.dt_collapse_updater ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_dt_updater_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim ts) :
    x = Eo.CRule.dt_updater_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_div_total_zero_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal ts) :
    x = Eo.CRule.arith_div_total_zero_real ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_div_total_zero_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint ts) :
    x = Eo.CRule.arith_div_total_zero_int ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_div_total {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal ts) :
    x = Eo.CRule.arith_int_div_total ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_div_total_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone ts) :
    x = Eo.CRule.arith_int_div_total_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_div_total_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero ts) :
    x = Eo.CRule.arith_int_div_total_zero ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_div_total_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg ts) :
    x = Eo.CRule.arith_int_div_total_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_mod_total {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal ts) :
    x = Eo.CRule.arith_int_mod_total ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_mod_total_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone ts) :
    x = Eo.CRule.arith_int_mod_total_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_mod_total_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero ts) :
    x = Eo.CRule.arith_int_mod_total_zero ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_mod_total_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg ts) :
    x = Eo.CRule.arith_int_mod_total_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_div_total_over_mod {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod ts) :
    x = Eo.CRule.arith_int_div_total_over_mod ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_elim_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt ts) :
    x = Eo.CRule.arith_elim_gt ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_elim_lt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt ts) :
    x = Eo.CRule.arith_elim_lt ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_elim_int_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt ts) :
    x = Eo.CRule.arith_elim_int_gt ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_elim_int_lt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt ts) :
    x = Eo.CRule.arith_elim_int_lt ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_elim_leq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq ts) :
    x = Eo.CRule.arith_elim_leq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_leq_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm ts) :
    x = Eo.CRule.arith_leq_norm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_geq_tighten {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten ts) :
    x = Eo.CRule.arith_geq_tighten ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_geq_norm1_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint ts) :
    x = Eo.CRule.arith_geq_norm1_int ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_geq_norm1_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal ts) :
    x = Eo.CRule.arith_geq_norm1_real ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_eq_elim_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal ts) :
    x = Eo.CRule.arith_eq_elim_real ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_eq_elim_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint ts) :
    x = Eo.CRule.arith_eq_elim_int ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_to_int_elim_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal ts) :
    x = Eo.CRule.arith_to_int_elim_to_real ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_is_int_elim_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal ts) :
    x = Eo.CRule.arith_is_int_elim_to_real ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_div_int_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal ts) :
    x = Eo.CRule.arith_div_int_to_real ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_div_total_int_to_real {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal ts) :
    x = Eo.CRule.arith_div_total_int_to_real ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mod_over_mod_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 ts) :
    x = Eo.CRule.arith_mod_over_mod_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mod_over_mod {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod ts) :
    x = Eo.CRule.arith_mod_over_mod ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_mod_over_mod_mult {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult ts) :
    x = Eo.CRule.arith_mod_over_mod_mult ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_eq_conflict {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict ts) :
    x = Eo.CRule.arith_int_eq_conflict ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_int_geq_tighten {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten ts) :
    x = Eo.CRule.arith_int_geq_tighten ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_divisible_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim ts) :
    x = Eo.CRule.arith_divisible_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_abs_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq ts) :
    x = Eo.CRule.arith_abs_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_abs_int_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt ts) :
    x = Eo.CRule.arith_abs_int_gt ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_abs_real_gt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt ts) :
    x = Eo.CRule.arith_abs_real_gt ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_geq_ite_lift {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift ts) :
    x = Eo.CRule.arith_geq_ite_lift ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_leq_ite_lift {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift ts) :
    x = Eo.CRule.arith_leq_ite_lift ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_min_lt1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 ts) :
    x = Eo.CRule.arith_min_lt1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_min_lt2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 ts) :
    x = Eo.CRule.arith_min_lt2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_max_geq1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 ts) :
    x = Eo.CRule.arith_max_geq1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_arith_max_geq2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 ts) :
    x = Eo.CRule.arith_max_geq2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_array_read_over_write {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite ts) :
    x = Eo.CRule.array_read_over_write ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_array_read_over_write2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 ts) :
    x = Eo.CRule.array_read_over_write2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_array_store_overwrite {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite ts) :
    x = Eo.CRule.array_store_overwrite ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_array_store_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself ts) :
    x = Eo.CRule.array_store_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_array_read_over_write_split {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit ts) :
    x = Eo.CRule.array_read_over_write_split ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_array_store_swap {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap ts) :
    x = Eo.CRule.array_store_swap ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_double_not_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim ts) :
    x = Eo.CRule.bool_double_not_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_not_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue ts) :
    x = Eo.CRule.bool_not_true ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_not_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse ts) :
    x = Eo.CRule.bool_not_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_eq_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue ts) :
    x = Eo.CRule.bool_eq_true ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_eq_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse ts) :
    x = Eo.CRule.bool_eq_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_eq_nrefl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl ts) :
    x = Eo.CRule.bool_eq_nrefl ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_impl_false1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 ts) :
    x = Eo.CRule.bool_impl_false1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_impl_false2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 ts) :
    x = Eo.CRule.bool_impl_false2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_impl_true1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 ts) :
    x = Eo.CRule.bool_impl_true1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_impl_true2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 ts) :
    x = Eo.CRule.bool_impl_true2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_impl_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim ts) :
    x = Eo.CRule.bool_impl_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_dual_impl_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq ts) :
    x = Eo.CRule.bool_dual_impl_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_and_conf {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf ts) :
    x = Eo.CRule.bool_and_conf ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_and_conf2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 ts) :
    x = Eo.CRule.bool_and_conf2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_or_taut {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut ts) :
    x = Eo.CRule.bool_or_taut ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_or_taut2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 ts) :
    x = Eo.CRule.bool_or_taut2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_or_de_morgan {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan ts) :
    x = Eo.CRule.bool_or_de_morgan ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_implies_de_morgan {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan ts) :
    x = Eo.CRule.bool_implies_de_morgan ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_and_de_morgan {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan ts) :
    x = Eo.CRule.bool_and_de_morgan ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_or_and_distrib {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib ts) :
    x = Eo.CRule.bool_or_and_distrib ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_implies_or_distrib {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib ts) :
    x = Eo.CRule.bool_implies_or_distrib ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_xor_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl ts) :
    x = Eo.CRule.bool_xor_refl ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_xor_nrefl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl ts) :
    x = Eo.CRule.bool_xor_nrefl ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_xor_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse ts) :
    x = Eo.CRule.bool_xor_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_xor_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue ts) :
    x = Eo.CRule.bool_xor_true ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_xor_comm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm ts) :
    x = Eo.CRule.bool_xor_comm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_xor_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim ts) :
    x = Eo.CRule.bool_xor_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_not_xor_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim ts) :
    x = Eo.CRule.bool_not_xor_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_not_eq_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 ts) :
    x = Eo.CRule.bool_not_eq_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_not_eq_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 ts) :
    x = Eo.CRule.bool_not_eq_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_neg_branch {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch ts) :
    x = Eo.CRule.ite_neg_branch ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_then_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue ts) :
    x = Eo.CRule.ite_then_true ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_else_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse ts) :
    x = Eo.CRule.ite_else_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_then_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse ts) :
    x = Eo.CRule.ite_then_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_else_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue ts) :
    x = Eo.CRule.ite_else_true ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_then_lookahead_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself ts) :
    x = Eo.CRule.ite_then_lookahead_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_else_lookahead_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself ts) :
    x = Eo.CRule.ite_else_lookahead_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_then_lookahead_not_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself ts) :
    x = Eo.CRule.ite_then_lookahead_not_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_else_lookahead_not_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself ts) :
    x = Eo.CRule.ite_else_lookahead_not_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_expand {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fexpand ts) :
    x = Eo.CRule.ite_expand ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bool_not_ite_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim ts) :
    x = Eo.CRule.bool_not_ite_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_true_cond {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond ts) :
    x = Eo.CRule.ite_true_cond ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_false_cond {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond ts) :
    x = Eo.CRule.ite_false_cond ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_not_cond {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond ts) :
    x = Eo.CRule.ite_not_cond ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_eq_branch {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch ts) :
    x = Eo.CRule.ite_eq_branch ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_then_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead ts) :
    x = Eo.CRule.ite_then_lookahead ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_else_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead ts) :
    x = Eo.CRule.ite_else_lookahead ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_then_neg_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead ts) :
    x = Eo.CRule.ite_then_neg_lookahead ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_ite_else_neg_lookahead {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead ts) :
    x = Eo.CRule.ite_else_neg_lookahead ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_concat_extract_merge {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge ts) :
    x = Eo.CRule.bv_concat_extract_merge ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_extract {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract ts) :
    x = Eo.CRule.bv_extract_extract ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_whole {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole ts) :
    x = Eo.CRule.bv_extract_whole ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_concat_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 ts) :
    x = Eo.CRule.bv_extract_concat_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_concat_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 ts) :
    x = Eo.CRule.bv_extract_concat_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_concat_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 ts) :
    x = Eo.CRule.bv_extract_concat_3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_concat_4 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 ts) :
    x = Eo.CRule.bv_extract_concat_4 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_eq_extract_elim1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 ts) :
    x = Eo.CRule.bv_eq_extract_elim1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_eq_extract_elim2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 ts) :
    x = Eo.CRule.bv_eq_extract_elim2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_eq_extract_elim3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 ts) :
    x = Eo.CRule.bv_eq_extract_elim3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_not {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot ts) :
    x = Eo.CRule.bv_extract_not ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_sign_extend_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 ts) :
    x = Eo.CRule.bv_extract_sign_extend_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_sign_extend_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 ts) :
    x = Eo.CRule.bv_extract_sign_extend_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_sign_extend_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 ts) :
    x = Eo.CRule.bv_extract_sign_extend_3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_not_xor {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor ts) :
    x = Eo.CRule.bv_not_xor ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_and_simplify_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 ts) :
    x = Eo.CRule.bv_and_simplify_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_and_simplify_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 ts) :
    x = Eo.CRule.bv_and_simplify_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_or_simplify_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 ts) :
    x = Eo.CRule.bv_or_simplify_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_or_simplify_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 ts) :
    x = Eo.CRule.bv_or_simplify_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_simplify_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 ts) :
    x = Eo.CRule.bv_xor_simplify_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_simplify_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 ts) :
    x = Eo.CRule.bv_xor_simplify_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_simplify_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 ts) :
    x = Eo.CRule.bv_xor_simplify_3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ult_add_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone ts) :
    x = Eo.CRule.bv_ult_add_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_mult_slt_mult_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 ts) :
    x = Eo.CRule.bv_mult_slt_mult_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_mult_slt_mult_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 ts) :
    x = Eo.CRule.bv_mult_slt_mult_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_commutative_xor {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor ts) :
    x = Eo.CRule.bv_commutative_xor ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_commutative_comp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp ts) :
    x = Eo.CRule.bv_commutative_comp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_zero_extend_eliminate_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 ts) :
    x = Eo.CRule.bv_zero_extend_eliminate_0 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sign_extend_eliminate_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 ts) :
    x = Eo.CRule.bv_sign_extend_eliminate_0 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_not_neq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq ts) :
    x = Eo.CRule.bv_not_neq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ult_ones {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones ts) :
    x = Eo.CRule.bv_ult_ones ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_concat_merge_const {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst ts) :
    x = Eo.CRule.bv_concat_merge_const ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_commutative_add {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd ts) :
    x = Eo.CRule.bv_commutative_add ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sub_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate ts) :
    x = Eo.CRule.bv_sub_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_width_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone ts) :
    x = Eo.CRule.bv_ite_width_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_width_one_not {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot ts) :
    x = Eo.CRule.bv_ite_width_one_not ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_eq_xor_solve {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve ts) :
    x = Eo.CRule.bv_eq_xor_solve ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_eq_not_solve {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve ts) :
    x = Eo.CRule.bv_eq_not_solve ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ugt_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate ts) :
    x = Eo.CRule.bv_ugt_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_uge_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate ts) :
    x = Eo.CRule.bv_uge_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sgt_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate ts) :
    x = Eo.CRule.bv_sgt_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sge_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate ts) :
    x = Eo.CRule.bv_sge_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sle_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate ts) :
    x = Eo.CRule.bv_sle_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_redor_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate ts) :
    x = Eo.CRule.bv_redor_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_redand_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate ts) :
    x = Eo.CRule.bv_redand_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ule_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate ts) :
    x = Eo.CRule.bv_ule_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_comp_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate ts) :
    x = Eo.CRule.bv_comp_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_rotate_left_eliminate_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 ts) :
    x = Eo.CRule.bv_rotate_left_eliminate_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_rotate_left_eliminate_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 ts) :
    x = Eo.CRule.bv_rotate_left_eliminate_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_rotate_right_eliminate_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 ts) :
    x = Eo.CRule.bv_rotate_right_eliminate_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_rotate_right_eliminate_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 ts) :
    x = Eo.CRule.bv_rotate_right_eliminate_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_nand_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate ts) :
    x = Eo.CRule.bv_nand_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_nor_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate ts) :
    x = Eo.CRule.bv_nor_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xnor_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate ts) :
    x = Eo.CRule.bv_xnor_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sdiv_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate ts) :
    x = Eo.CRule.bv_sdiv_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_zero_extend_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate ts) :
    x = Eo.CRule.bv_zero_extend_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_uaddo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate ts) :
    x = Eo.CRule.bv_uaddo_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_saddo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate ts) :
    x = Eo.CRule.bv_saddo_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sdivo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate ts) :
    x = Eo.CRule.bv_sdivo_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_smod_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate ts) :
    x = Eo.CRule.bv_smod_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_srem_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate ts) :
    x = Eo.CRule.bv_srem_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_usubo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate ts) :
    x = Eo.CRule.bv_usubo_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ssubo_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate ts) :
    x = Eo.CRule.bv_ssubo_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_nego_eliminate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate ts) :
    x = Eo.CRule.bv_nego_eliminate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_equal_children {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren ts) :
    x = Eo.CRule.bv_ite_equal_children ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_const_cond_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 ts) :
    x = Eo.CRule.bv_ite_const_cond_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_const_cond_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 ts) :
    x = Eo.CRule.bv_ite_const_cond_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_const_children_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 ts) :
    x = Eo.CRule.bv_ite_const_children_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_const_children_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 ts) :
    x = Eo.CRule.bv_ite_const_children_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_equal_cond_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 ts) :
    x = Eo.CRule.bv_ite_equal_cond_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_equal_cond_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 ts) :
    x = Eo.CRule.bv_ite_equal_cond_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_equal_cond_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 ts) :
    x = Eo.CRule.bv_ite_equal_cond_3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_merge_then_if {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif ts) :
    x = Eo.CRule.bv_ite_merge_then_if ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_merge_else_if {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif ts) :
    x = Eo.CRule.bv_ite_merge_else_if ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_merge_then_else {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse ts) :
    x = Eo.CRule.bv_ite_merge_then_else ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ite_merge_else_else {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse ts) :
    x = Eo.CRule.bv_ite_merge_else_else ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_shl_by_const_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 ts) :
    x = Eo.CRule.bv_shl_by_const_0 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_shl_by_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 ts) :
    x = Eo.CRule.bv_shl_by_const_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_shl_by_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 ts) :
    x = Eo.CRule.bv_shl_by_const_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_lshr_by_const_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 ts) :
    x = Eo.CRule.bv_lshr_by_const_0 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_lshr_by_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 ts) :
    x = Eo.CRule.bv_lshr_by_const_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_lshr_by_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 ts) :
    x = Eo.CRule.bv_lshr_by_const_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ashr_by_const_0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 ts) :
    x = Eo.CRule.bv_ashr_by_const_0 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ashr_by_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 ts) :
    x = Eo.CRule.bv_ashr_by_const_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ashr_by_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 ts) :
    x = Eo.CRule.bv_ashr_by_const_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_and_concat_pullup {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup ts) :
    x = Eo.CRule.bv_and_concat_pullup ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_or_concat_pullup {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup ts) :
    x = Eo.CRule.bv_or_concat_pullup ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_concat_pullup {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup ts) :
    x = Eo.CRule.bv_xor_concat_pullup ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_and_concat_pullup2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 ts) :
    x = Eo.CRule.bv_and_concat_pullup2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_or_concat_pullup2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 ts) :
    x = Eo.CRule.bv_or_concat_pullup2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_concat_pullup2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 ts) :
    x = Eo.CRule.bv_xor_concat_pullup2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_and_concat_pullup3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 ts) :
    x = Eo.CRule.bv_and_concat_pullup3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_or_concat_pullup3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 ts) :
    x = Eo.CRule.bv_or_concat_pullup3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_concat_pullup3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 ts) :
    x = Eo.CRule.bv_xor_concat_pullup3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_duplicate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate ts) :
    x = Eo.CRule.bv_xor_duplicate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_ones {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones ts) :
    x = Eo.CRule.bv_xor_ones ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_xor_not {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot ts) :
    x = Eo.CRule.bv_xor_not ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_not_idemp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp ts) :
    x = Eo.CRule.bv_not_idemp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ult_zero_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 ts) :
    x = Eo.CRule.bv_ult_zero_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ult_zero_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 ts) :
    x = Eo.CRule.bv_ult_zero_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ult_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself ts) :
    x = Eo.CRule.bv_ult_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_lt_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself ts) :
    x = Eo.CRule.bv_lt_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ule_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself ts) :
    x = Eo.CRule.bv_ule_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ule_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero ts) :
    x = Eo.CRule.bv_ule_zero ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_zero_ule {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule ts) :
    x = Eo.CRule.bv_zero_ule ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sle_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself ts) :
    x = Eo.CRule.bv_sle_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ule_max {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax ts) :
    x = Eo.CRule.bv_ule_max ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_not_ult {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult ts) :
    x = Eo.CRule.bv_not_ult ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_mult_pow2_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 ts) :
    x = Eo.CRule.bv_mult_pow2_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_mult_pow2_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 ts) :
    x = Eo.CRule.bv_mult_pow2_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_mult_pow2_2b {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b ts) :
    x = Eo.CRule.bv_mult_pow2_2b ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_extract_mult_leading_bit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit ts) :
    x = Eo.CRule.bv_extract_mult_leading_bit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_udiv_pow2_not_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone ts) :
    x = Eo.CRule.bv_udiv_pow2_not_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_udiv_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero ts) :
    x = Eo.CRule.bv_udiv_zero ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_udiv_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone ts) :
    x = Eo.CRule.bv_udiv_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_urem_pow2_not_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone ts) :
    x = Eo.CRule.bv_urem_pow2_not_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_urem_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone ts) :
    x = Eo.CRule.bv_urem_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_urem_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself ts) :
    x = Eo.CRule.bv_urem_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_shl_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero ts) :
    x = Eo.CRule.bv_shl_zero ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_lshr_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero ts) :
    x = Eo.CRule.bv_lshr_zero ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ashr_zero {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero ts) :
    x = Eo.CRule.bv_ashr_zero ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ugt_urem {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem ts) :
    x = Eo.CRule.bv_ugt_urem ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_ult_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone ts) :
    x = Eo.CRule.bv_ult_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_merge_sign_extend_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 ts) :
    x = Eo.CRule.bv_merge_sign_extend_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_merge_sign_extend_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 ts) :
    x = Eo.CRule.bv_merge_sign_extend_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sign_extend_eq_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 ts) :
    x = Eo.CRule.bv_sign_extend_eq_const_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sign_extend_eq_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 ts) :
    x = Eo.CRule.bv_sign_extend_eq_const_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_zero_extend_eq_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 ts) :
    x = Eo.CRule.bv_zero_extend_eq_const_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_zero_extend_eq_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 ts) :
    x = Eo.CRule.bv_zero_extend_eq_const_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_zero_extend_ult_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 ts) :
    x = Eo.CRule.bv_zero_extend_ult_const_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_zero_extend_ult_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 ts) :
    x = Eo.CRule.bv_zero_extend_ult_const_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sign_extend_ult_const_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 ts) :
    x = Eo.CRule.bv_sign_extend_ult_const_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sign_extend_ult_const_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 ts) :
    x = Eo.CRule.bv_sign_extend_ult_const_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sign_extend_ult_const_3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 ts) :
    x = Eo.CRule.bv_sign_extend_ult_const_3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_bv_sign_extend_ult_const_4 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 ts) :
    x = Eo.CRule.bv_sign_extend_ult_const_4 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_eq_singleton_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp ts) :
    x = Eo.CRule.sets_eq_singleton_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_member_singleton {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton ts) :
    x = Eo.CRule.sets_member_singleton ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_member_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp ts) :
    x = Eo.CRule.sets_member_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_subset_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim ts) :
    x = Eo.CRule.sets_subset_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_insert_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim ts) :
    x = Eo.CRule.sets_insert_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_union_comm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm ts) :
    x = Eo.CRule.sets_union_comm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_inter_comm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm ts) :
    x = Eo.CRule.sets_inter_comm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_inter_emp1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 ts) :
    x = Eo.CRule.sets_inter_emp1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_inter_emp2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 ts) :
    x = Eo.CRule.sets_inter_emp2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_minus_emp1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 ts) :
    x = Eo.CRule.sets_minus_emp1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_minus_emp2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 ts) :
    x = Eo.CRule.sets_minus_emp2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_union_emp1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 ts) :
    x = Eo.CRule.sets_union_emp1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_union_emp2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 ts) :
    x = Eo.CRule.sets_union_emp2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_inter_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember ts) :
    x = Eo.CRule.sets_inter_member ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_minus_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember ts) :
    x = Eo.CRule.sets_minus_member ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_union_member {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember ts) :
    x = Eo.CRule.sets_union_member ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_choose_singleton {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton ts) :
    x = Eo.CRule.sets_choose_singleton ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_minus_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself ts) :
    x = Eo.CRule.sets_minus_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_union_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself ts) :
    x = Eo.CRule.sets_union_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_inter_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself ts) :
    x = Eo.CRule.sets_inter_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_is_empty_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim ts) :
    x = Eo.CRule.sets_is_empty_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_sets_is_singleton_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim ts) :
    x = Eo.CRule.sets_is_singleton_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_ctn_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse ts) :
    x = Eo.CRule.str_eq_ctn_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_ctn_full_false1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 ts) :
    x = Eo.CRule.str_eq_ctn_full_false1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_ctn_full_false2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 ts) :
    x = Eo.CRule.str_eq_ctn_full_false2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_len_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse ts) :
    x = Eo.CRule.str_eq_len_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_empty_str {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr ts) :
    x = Eo.CRule.str_substr_empty_str ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_empty_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange ts) :
    x = Eo.CRule.str_substr_empty_range ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_empty_start {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart ts) :
    x = Eo.CRule.str_substr_empty_start ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_empty_start_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg ts) :
    x = Eo.CRule.str_substr_empty_start_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_substr_start_geq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen ts) :
    x = Eo.CRule.str_substr_substr_start_geq_len ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_eq_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty ts) :
    x = Eo.CRule.str_substr_eq_empty ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_z_eq_empty_leq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq ts) :
    x = Eo.CRule.str_substr_z_eq_empty_leq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_eq_empty_leq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen ts) :
    x = Eo.CRule.str_substr_eq_empty_leq_len ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_len_replace_inv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv ts) :
    x = Eo.CRule.str_len_replace_inv ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_len_replace_all_inv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv ts) :
    x = Eo.CRule.str_len_replace_all_inv ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_len_update_inv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv ts) :
    x = Eo.CRule.str_len_update_inv ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_update_oob {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob ts) :
    x = Eo.CRule.str_update_oob ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_update_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev ts) :
    x = Eo.CRule.str_update_rev ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_update_fit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit ts) :
    x = Eo.CRule.str_update_fit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_update_concat_fit0 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 ts) :
    x = Eo.CRule.str_update_concat_fit0 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_update_concat_fit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit ts) :
    x = Eo.CRule.str_update_concat_fit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_update_in_first_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat ts) :
    x = Eo.CRule.str_update_in_first_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_len_substr_in_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange ts) :
    x = Eo.CRule.str_len_substr_in_range ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_clash {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash ts) :
    x = Eo.CRule.str_concat_clash ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_clash_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev ts) :
    x = Eo.CRule.str_concat_clash_rev ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_clash2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 ts) :
    x = Eo.CRule.str_concat_clash2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_clash2_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev ts) :
    x = Eo.CRule.str_concat_clash2_rev ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_unify {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify ts) :
    x = Eo.CRule.str_concat_unify ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_unify_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev ts) :
    x = Eo.CRule.str_concat_unify_rev ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_unify_base {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase ts) :
    x = Eo.CRule.str_concat_unify_base ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_concat_unify_base_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev ts) :
    x = Eo.CRule.str_concat_unify_base_rev ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_prefixof_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim ts) :
    x = Eo.CRule.str_prefixof_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_suffixof_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim ts) :
    x = Eo.CRule.str_suffixof_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_prefixof_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq ts) :
    x = Eo.CRule.str_prefixof_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_suffixof_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq ts) :
    x = Eo.CRule.str_suffixof_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_prefixof_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone ts) :
    x = Eo.CRule.str_prefixof_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_suffixof_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone ts) :
    x = Eo.CRule.str_suffixof_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_combine1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 ts) :
    x = Eo.CRule.str_substr_combine1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_combine2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 ts) :
    x = Eo.CRule.str_substr_combine2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_combine3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 ts) :
    x = Eo.CRule.str_substr_combine3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_combine4 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 ts) :
    x = Eo.CRule.str_substr_combine4 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_concat1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 ts) :
    x = Eo.CRule.str_substr_concat1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_concat2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 ts) :
    x = Eo.CRule.str_substr_concat2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_replace {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace ts) :
    x = Eo.CRule.str_substr_replace ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_full {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull ts) :
    x = Eo.CRule.str_substr_full ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_full_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq ts) :
    x = Eo.CRule.str_substr_full_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl ts) :
    x = Eo.CRule.str_contains_refl ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_concat_find {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind ts) :
    x = Eo.CRule.str_contains_concat_find ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_concat_find_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra ts) :
    x = Eo.CRule.str_contains_concat_find_contra ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_split_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar ts) :
    x = Eo.CRule.str_contains_split_char ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_leq_len_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq ts) :
    x = Eo.CRule.str_contains_leq_len_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp ts) :
    x = Eo.CRule.str_contains_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar ts) :
    x = Eo.CRule.str_contains_char ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_at_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim ts) :
    x = Eo.CRule.str_at_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself ts) :
    x = Eo.CRule.str_replace_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_id {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid ts) :
    x = Eo.CRule.str_replace_id ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_prefix {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix ts) :
    x = Eo.CRule.str_replace_prefix ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_prefix_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat ts) :
    x = Eo.CRule.str_replace_prefix_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_no_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains ts) :
    x = Eo.CRule.str_replace_no_contains ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_find_base {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase ts) :
    x = Eo.CRule.str_replace_find_base ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_find_first_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat ts) :
    x = Eo.CRule.str_replace_find_first_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty ts) :
    x = Eo.CRule.str_replace_empty ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_one_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre ts) :
    x = Eo.CRule.str_replace_one_pre ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_find_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre ts) :
    x = Eo.CRule.str_replace_find_pre ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_all_no_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains ts) :
    x = Eo.CRule.str_replace_all_no_contains ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_all_find_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre ts) :
    x = Eo.CRule.str_replace_all_find_pre ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_all_find {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind ts) :
    x = Eo.CRule.str_replace_all_find ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_all_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty ts) :
    x = Eo.CRule.str_replace_all_empty ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_all_id {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid ts) :
    x = Eo.CRule.str_replace_all_id ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_all_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself ts) :
    x = Eo.CRule.str_replace_all_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_re_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone ts) :
    x = Eo.CRule.str_replace_re_none ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_re_all_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone ts) :
    x = Eo.CRule.str_replace_re_all_none ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_len_concat_rec {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec ts) :
    x = Eo.CRule.str_len_concat_rec ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_len_eq_zero_concat_rec {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec ts) :
    x = Eo.CRule.str_len_eq_zero_concat_rec ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_len_eq_zero_base {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase ts) :
    x = Eo.CRule.str_len_eq_zero_base ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself ts) :
    x = Eo.CRule.str_indexof_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_no_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains ts) :
    x = Eo.CRule.str_indexof_no_contains ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_oob {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob ts) :
    x = Eo.CRule.str_indexof_oob ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_oob2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 ts) :
    x = Eo.CRule.str_indexof_oob2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_contains_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre ts) :
    x = Eo.CRule.str_indexof_contains_pre ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_contains_concat_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre ts) :
    x = Eo.CRule.str_indexof_contains_concat_pre ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_prefix_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat ts) :
    x = Eo.CRule.str_indexof_prefix_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_len_oob {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob ts) :
    x = Eo.CRule.str_indexof_len_oob ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_len_oob2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 ts) :
    x = Eo.CRule.str_indexof_len_oob2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_find_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp ts) :
    x = Eo.CRule.str_indexof_find_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_eq_irr {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr ts) :
    x = Eo.CRule.str_indexof_eq_irr ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_re_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone ts) :
    x = Eo.CRule.str_indexof_re_none ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_indexof_re_emp_re {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre ts) :
    x = Eo.CRule.str_indexof_re_emp_re ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_lower_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat ts) :
    x = Eo.CRule.str_to_lower_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_upper_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat ts) :
    x = Eo.CRule.str_to_upper_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_lower_upper {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper ts) :
    x = Eo.CRule.str_to_lower_upper ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_lower_idem {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem ts) :
    x = Eo.CRule.str_to_lower_idem ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_upper_lower {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower ts) :
    x = Eo.CRule.str_to_upper_lower ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_upper_idem {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem ts) :
    x = Eo.CRule.str_to_upper_idem ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_lower_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen ts) :
    x = Eo.CRule.str_to_lower_len ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_upper_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen ts) :
    x = Eo.CRule.str_to_upper_len ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_lower_from_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint ts) :
    x = Eo.CRule.str_to_lower_from_int ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_upper_from_int {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint ts) :
    x = Eo.CRule.str_to_upper_from_int ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_to_int_concat_neg_one {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone ts) :
    x = Eo.CRule.str_to_int_concat_neg_one ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_is_digit_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim ts) :
    x = Eo.CRule.str_is_digit_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_leq_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty ts) :
    x = Eo.CRule.str_leq_empty ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_leq_empty_eq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq ts) :
    x = Eo.CRule.str_leq_empty_eq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_leq_concat_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse ts) :
    x = Eo.CRule.str_leq_concat_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_leq_concat_true {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue ts) :
    x = Eo.CRule.str_leq_concat_true ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_leq_concat_base_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 ts) :
    x = Eo.CRule.str_leq_concat_base_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_leq_concat_base_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 ts) :
    x = Eo.CRule.str_leq_concat_base_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_lt_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim ts) :
    x = Eo.CRule.str_lt_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_from_int_no_ctn_nondigit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit ts) :
    x = Eo.CRule.str_from_int_no_ctn_nondigit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_ctn_contra {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra ts) :
    x = Eo.CRule.str_substr_ctn_contra ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn ts) :
    x = Eo.CRule.str_substr_ctn ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_dual_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn ts) :
    x = Eo.CRule.str_replace_dual_ctn ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_dual_ctn_false {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse ts) :
    x = Eo.CRule.str_replace_dual_ctn_false ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_self_ctn_simp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp ts) :
    x = Eo.CRule.str_replace_self_ctn_simp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_replace_emp_ctn_src {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc ts) :
    x = Eo.CRule.str_replace_emp_ctn_src ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_char_start_eq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen ts) :
    x = Eo.CRule.str_substr_char_start_eq_len ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_repl_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar ts) :
    x = Eo.CRule.str_contains_repl_char ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_repl_self_tgt_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar ts) :
    x = Eo.CRule.str_contains_repl_self_tgt_char ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_repl_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself ts) :
    x = Eo.CRule.str_contains_repl_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_contains_repl_tgt {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt ts) :
    x = Eo.CRule.str_contains_repl_tgt ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_len_id {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid ts) :
    x = Eo.CRule.str_repl_repl_len_id ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_src_tgt_no_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn ts) :
    x = Eo.CRule.str_repl_repl_src_tgt_no_ctn ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_tgt_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself ts) :
    x = Eo.CRule.str_repl_repl_tgt_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_tgt_no_ctn {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn ts) :
    x = Eo.CRule.str_repl_repl_tgt_no_ctn ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_src_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself ts) :
    x = Eo.CRule.str_repl_repl_src_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_src_inv_no_ctn1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 ts) :
    x = Eo.CRule.str_repl_repl_src_inv_no_ctn1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_src_inv_no_ctn2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 ts) :
    x = Eo.CRule.str_repl_repl_src_inv_no_ctn2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_src_inv_no_ctn3 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 ts) :
    x = Eo.CRule.str_repl_repl_src_inv_no_ctn3 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_dual_self {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself ts) :
    x = Eo.CRule.str_repl_repl_dual_self ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_dual_ite1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 ts) :
    x = Eo.CRule.str_repl_repl_dual_ite1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_dual_ite2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 ts) :
    x = Eo.CRule.str_repl_repl_dual_ite2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_repl_repl_lookahead_id_simp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp ts) :
    x = Eo.CRule.str_repl_repl_lookahead_id_simp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_all_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim ts) :
    x = Eo.CRule.re_all_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_opt_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim ts) :
    x = Eo.CRule.re_opt_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_diff_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim ts) :
    x = Eo.CRule.re_diff_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_plus_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim ts) :
    x = Eo.CRule.re_plus_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_repeat_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim ts) :
    x = Eo.CRule.re_repeat_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_concat_star_swap {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap ts) :
    x = Eo.CRule.re_concat_star_swap ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_concat_star_repeat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat ts) :
    x = Eo.CRule.re_concat_star_repeat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_concat_star_nullable1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 ts) :
    x = Eo.CRule.re_concat_star_nullable1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_concat_star_nullable2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 ts) :
    x = Eo.CRule.re_concat_star_nullable2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_concat_merge {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge ts) :
    x = Eo.CRule.re_concat_merge ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_union_all {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall ts) :
    x = Eo.CRule.re_union_all ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_union_const_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim ts) :
    x = Eo.CRule.re_union_const_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_inter_all {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall ts) :
    x = Eo.CRule.re_inter_all ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_star_none {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone ts) :
    x = Eo.CRule.re_star_none ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_star_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp ts) :
    x = Eo.CRule.re_star_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_star_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar ts) :
    x = Eo.CRule.re_star_star ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_range_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl ts) :
    x = Eo.CRule.re_range_refl ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_range_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp ts) :
    x = Eo.CRule.re_range_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_range_non_singleton_1 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 ts) :
    x = Eo.CRule.re_range_non_singleton_1 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_range_non_singleton_2 {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 ts) :
    x = Eo.CRule.re_range_non_singleton_2 ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_star_union_char {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar ts) :
    x = Eo.CRule.re_star_union_char ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_star_union_drop_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp ts) :
    x = Eo.CRule.re_star_union_drop_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_loop_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg ts) :
    x = Eo.CRule.re_loop_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_loop_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar ts) :
    x = Eo.CRule.re_loop_star ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_inter_cstring {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring ts) :
    x = Eo.CRule.re_inter_cstring ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_inter_cstring_neg {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg ts) :
    x = Eo.CRule.re_inter_cstring_neg ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_len_include {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude ts) :
    x = Eo.CRule.str_substr_len_include ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_len_include_pre {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre ts) :
    x = Eo.CRule.str_substr_len_include_pre ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_substr_len_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm ts) :
    x = Eo.CRule.str_substr_len_norm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_len_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev ts) :
    x = Eo.CRule.seq_len_rev ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_rev_rev {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev ts) :
    x = Eo.CRule.seq_rev_rev ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_rev_concat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat ts) :
    x = Eo.CRule.seq_rev_concat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_repl_self_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp ts) :
    x = Eo.CRule.str_eq_repl_self_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_repl_no_change {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange ts) :
    x = Eo.CRule.str_eq_repl_no_change ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_repl_tgt_eq_len {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen ts) :
    x = Eo.CRule.str_eq_repl_tgt_eq_len ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_repl_len_one_emp_prefix {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix ts) :
    x = Eo.CRule.str_eq_repl_len_one_emp_prefix ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_repl_emp_tgt_nemp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp ts) :
    x = Eo.CRule.str_eq_repl_emp_tgt_nemp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_repl_nemp_src_emp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp ts) :
    x = Eo.CRule.str_eq_repl_nemp_src_emp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_eq_repl_self_src {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc ts) :
    x = Eo.CRule.str_eq_repl_self_src ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_len_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit ts) :
    x = Eo.CRule.seq_len_unit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_nth_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit ts) :
    x = Eo.CRule.seq_nth_unit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_nth_concat_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit ts) :
    x = Eo.CRule.seq_nth_concat_unit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_nth_concat_unit_gen {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen ts) :
    x = Eo.CRule.seq_nth_concat_unit_gen ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_seq_rev_unit {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit ts) :
    x = Eo.CRule.seq_rev_unit ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_in_empty {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty ts) :
    x = Eo.CRule.re_in_empty ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_in_sigma {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma ts) :
    x = Eo.CRule.re_in_sigma ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_in_sigma_star {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar ts) :
    x = Eo.CRule.re_in_sigma_star ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_in_cstring {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring ts) :
    x = Eo.CRule.re_in_cstring ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_re_in_comp {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp ts) :
    x = Eo.CRule.re_in_comp ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_union_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim ts) :
    x = Eo.CRule.str_in_re_union_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_inter_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim ts) :
    x = Eo.CRule.str_in_re_inter_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_range_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim ts) :
    x = Eo.CRule.str_in_re_range_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_contains {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains ts) :
    x = Eo.CRule.str_in_re_contains ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_from_int_nemp_dig_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange ts) :
    x = Eo.CRule.str_in_re_from_int_nemp_dig_range ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_str_in_re_from_int_dig_range {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange ts) :
    x = Eo.CRule.str_in_re_from_int_dig_range ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_eq_refl {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5frefl ts) :
    x = Eo.CRule.eq_refl ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_eq_symm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fsymm ts) :
    x = Eo.CRule.eq_symm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_eq_cond_deq {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq ts) :
    x = Eo.CRule.eq_cond_deq ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_eq_ite_lift {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift ts) :
    x = Eo.CRule.eq_ite_lift ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_distinct_binary_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim ts) :
    x = Eo.CRule.distinct_binary_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_bv2nat_int2bv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv ts) :
    x = Eo.CRule.uf_bv2nat_int2bv ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_bv2nat_int2bv_extend {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend ts) :
    x = Eo.CRule.uf_bv2nat_int2bv_extend ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_bv2nat_int2bv_extract {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract ts) :
    x = Eo.CRule.uf_bv2nat_int2bv_extract ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_int2bv_bv2nat {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat ts) :
    x = Eo.CRule.uf_int2bv_bv2nat ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_bv2nat_geq_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim ts) :
    x = Eo.CRule.uf_bv2nat_geq_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_int2bv_bvult_equiv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv ts) :
    x = Eo.CRule.uf_int2bv_bvult_equiv ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_int2bv_bvule_equiv {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv ts) :
    x = Eo.CRule.uf_int2bv_bvule_equiv ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_uf_sbv_to_int_elim {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim ts) :
    x = Eo.CRule.uf_sbv_to_int_elim ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_evaluate {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eevaluate ts) :
    x = Eo.CRule.evaluate ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_distinct_values {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues ts) :
    x = Eo.CRule.distinct_values ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_aci_norm {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eaci_5fnorm ts) :
    x = Eo.CRule.aci_norm ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_absorb {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2eabsorb ts) :
    x = Eo.CRule.absorb ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

theorem inv_CRule_distinct_card_conflict {x : Eo.CRule} {ts : List Tree}
    (h : enc_CRule x = Tree.node schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict ts) :
    x = Eo.CRule.distinct_card_conflict ∧ ts = [] := by
  cases x <;> simp_all [enc_CRule]

mutual
theorem dec_enc_CRule : (x : Eo.CRule) → emb_CRule x → dec_CRule (enc_CRule x) = some x
  | Eo.CRule.scope, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.process_scope, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.split, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.resolution, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.chain_resolution, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.chain_m_resolution, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.factoring, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.reordering, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.eq_resolve, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.modus_ponens, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_not_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.contra, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.and_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.and_intro, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_or_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.implies_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_implies_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_implies_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.equiv_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.equiv_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_equiv_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_equiv_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.xor_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.xor_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_xor_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_xor_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_ite_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_ite_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.not_and, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_and_pos, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_and_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_or_pos, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_or_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_implies_pos, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_implies_neg1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_implies_neg2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_equiv_pos1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_equiv_pos2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_equiv_neg1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_equiv_neg2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_xor_pos1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_xor_pos2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_xor_neg1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_xor_neg2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_ite_pos1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_ite_pos2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_ite_pos3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_ite_neg1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_ite_neg2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cnf_ite_neg3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arrays_read_over_write, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arrays_read_over_write_contra, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arrays_read_over_write_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arrays_ext, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.refl, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.symm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.trans, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.cong, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.nary_cong, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.pairwise_cong, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.true_intro, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.true_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.false_intro, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.false_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ho_cong, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.distinct_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.distinct_true, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.distinct_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_sum_ub, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mult_pos, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mult_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_trichotomy, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.int_tight_ub, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.int_tight_lb, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mult_tangent, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mult_sign, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mult_abs_comparison, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_reduction, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_poly_norm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_poly_norm_rel, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_repeat_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_smulo_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_umulo_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_bitwise_slicing, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_bitblast_step, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_poly_norm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_poly_norm_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_length_pos, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_length_non_empty, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.concat_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.concat_unify, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.concat_csplit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.concat_split, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.concat_lprop, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.concat_cprop, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_decompose, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.exists_string_length, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_code_inj, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_seq_unit_inj, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_inter, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_unfold_pos, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_unfold_neg_concat_fixed, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_unfold_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_ext, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_reduction, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.string_eager_reduction, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_string_pred_entail, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_string_pred_safe_approx, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_eval, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_consume, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_loop_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_eq_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_inter_inclusion, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_union_inclusion, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_concat_star_char, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_sigma, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_sigma_star, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_ctn_multiset_subset, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_overlap_split_ctn, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_overlap_endpoints_ctn, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_overlap_endpoints_indexof, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_overlap_endpoints_replace, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_re_eval, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_re_eval, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_re_all_eval, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_eval_op, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_singleton_inj, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_ext, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_choose_member, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_eval_op, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ubv_to_int_range, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ubv_to_int_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.int_to_bv_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.instantiate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.skolemize, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.skolem_intro, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.alpha_equiv, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.beta_reduce, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_var_reordering, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.exists_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_unused_vars, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_merge_prenex, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_miniscope_and, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_miniscope_or, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_miniscope_ite, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_var_elim_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.quant_dt_split, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_split, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_inst, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_collapse_selector, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_collapse_tester, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_collapse_tester_singleton, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_cons_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_cons_eq_clash, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_cycle, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_collapse_updater, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.dt_updater_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_div_total_zero_real, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_div_total_zero_int, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_div_total, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_div_total_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_div_total_zero, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_div_total_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_mod_total, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_mod_total_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_mod_total_zero, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_mod_total_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_div_total_over_mod, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_elim_gt, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_elim_lt, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_elim_int_gt, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_elim_int_lt, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_elim_leq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_leq_norm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_geq_tighten, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_geq_norm1_int, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_geq_norm1_real, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_eq_elim_real, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_eq_elim_int, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_to_int_elim_to_real, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_is_int_elim_to_real, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_div_int_to_real, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_div_total_int_to_real, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mod_over_mod_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mod_over_mod, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_mod_over_mod_mult, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_eq_conflict, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_int_geq_tighten, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_divisible_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_abs_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_abs_int_gt, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_abs_real_gt, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_geq_ite_lift, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_leq_ite_lift, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_min_lt1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_min_lt2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_max_geq1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.arith_max_geq2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.array_read_over_write, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.array_read_over_write2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.array_store_overwrite, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.array_store_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.array_read_over_write_split, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.array_store_swap, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_double_not_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_not_true, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_not_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_eq_true, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_eq_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_eq_nrefl, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_impl_false1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_impl_false2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_impl_true1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_impl_true2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_impl_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_dual_impl_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_and_conf, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_and_conf2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_or_taut, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_or_taut2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_or_de_morgan, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_implies_de_morgan, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_and_de_morgan, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_or_and_distrib, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_implies_or_distrib, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_xor_refl, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_xor_nrefl, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_xor_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_xor_true, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_xor_comm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_xor_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_not_xor_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_not_eq_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_not_eq_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_neg_branch, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_then_true, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_else_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_then_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_else_true, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_then_lookahead_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_else_lookahead_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_then_lookahead_not_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_else_lookahead_not_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_expand, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bool_not_ite_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_true_cond, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_false_cond, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_not_cond, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_eq_branch, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_then_lookahead, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_else_lookahead, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_then_neg_lookahead, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.ite_else_neg_lookahead, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_concat_extract_merge, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_extract, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_whole, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_concat_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_concat_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_concat_3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_concat_4, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_eq_extract_elim1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_eq_extract_elim2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_eq_extract_elim3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_not, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_sign_extend_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_sign_extend_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_sign_extend_3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_not_xor, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_and_simplify_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_and_simplify_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_or_simplify_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_or_simplify_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_simplify_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_simplify_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_simplify_3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ult_add_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_mult_slt_mult_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_mult_slt_mult_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_commutative_xor, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_commutative_comp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_zero_extend_eliminate_0, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sign_extend_eliminate_0, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_not_neq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ult_ones, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_concat_merge_const, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_commutative_add, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sub_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_width_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_width_one_not, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_eq_xor_solve, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_eq_not_solve, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ugt_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_uge_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sgt_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sge_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sle_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_redor_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_redand_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ule_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_comp_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_rotate_left_eliminate_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_rotate_left_eliminate_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_rotate_right_eliminate_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_rotate_right_eliminate_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_nand_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_nor_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xnor_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sdiv_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_zero_extend_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_uaddo_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_saddo_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sdivo_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_smod_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_srem_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_usubo_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ssubo_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_nego_eliminate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_equal_children, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_const_cond_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_const_cond_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_const_children_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_const_children_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_equal_cond_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_equal_cond_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_equal_cond_3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_merge_then_if, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_merge_else_if, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_merge_then_else, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ite_merge_else_else, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_shl_by_const_0, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_shl_by_const_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_shl_by_const_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_lshr_by_const_0, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_lshr_by_const_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_lshr_by_const_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ashr_by_const_0, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ashr_by_const_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ashr_by_const_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_and_concat_pullup, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_or_concat_pullup, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_concat_pullup, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_and_concat_pullup2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_or_concat_pullup2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_concat_pullup2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_and_concat_pullup3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_or_concat_pullup3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_concat_pullup3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_duplicate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_ones, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_xor_not, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_not_idemp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ult_zero_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ult_zero_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ult_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_lt_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ule_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ule_zero, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_zero_ule, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sle_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ule_max, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_not_ult, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_mult_pow2_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_mult_pow2_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_mult_pow2_2b, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_extract_mult_leading_bit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_udiv_pow2_not_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_udiv_zero, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_udiv_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_urem_pow2_not_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_urem_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_urem_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_shl_zero, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_lshr_zero, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ashr_zero, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ugt_urem, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_ult_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_merge_sign_extend_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_merge_sign_extend_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sign_extend_eq_const_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sign_extend_eq_const_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_zero_extend_eq_const_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_zero_extend_eq_const_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_zero_extend_ult_const_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_zero_extend_ult_const_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sign_extend_ult_const_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sign_extend_ult_const_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sign_extend_ult_const_3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.bv_sign_extend_ult_const_4, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_eq_singleton_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_member_singleton, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_member_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_subset_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_insert_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_union_comm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_inter_comm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_inter_emp1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_inter_emp2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_minus_emp1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_minus_emp2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_union_emp1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_union_emp2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_inter_member, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_minus_member, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_union_member, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_choose_singleton, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_minus_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_union_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_inter_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_is_empty_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.sets_is_singleton_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_ctn_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_ctn_full_false1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_ctn_full_false2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_len_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_empty_str, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_empty_range, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_empty_start, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_empty_start_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_substr_start_geq_len, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_eq_empty, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_z_eq_empty_leq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_eq_empty_leq_len, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_len_replace_inv, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_len_replace_all_inv, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_len_update_inv, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_update_oob, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_update_rev, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_update_fit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_update_concat_fit0, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_update_concat_fit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_update_in_first_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_len_substr_in_range, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_clash, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_clash_rev, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_clash2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_clash2_rev, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_unify, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_unify_rev, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_unify_base, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_concat_unify_base_rev, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_prefixof_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_suffixof_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_prefixof_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_suffixof_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_prefixof_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_suffixof_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_combine1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_combine2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_combine3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_combine4, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_concat1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_concat2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_replace, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_full, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_full_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_refl, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_concat_find, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_concat_find_contra, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_split_char, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_leq_len_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_char, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_at_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_id, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_prefix, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_prefix_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_no_contains, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_find_base, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_find_first_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_empty, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_one_pre, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_find_pre, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_all_no_contains, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_all_find_pre, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_all_find, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_all_empty, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_all_id, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_all_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_re_none, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_re_all_none, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_len_concat_rec, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_len_eq_zero_concat_rec, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_len_eq_zero_base, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_no_contains, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_oob, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_oob2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_contains_pre, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_contains_concat_pre, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_prefix_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_len_oob, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_len_oob2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_find_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_eq_irr, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_re_none, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_indexof_re_emp_re, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_lower_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_upper_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_lower_upper, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_lower_idem, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_upper_lower, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_upper_idem, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_lower_len, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_upper_len, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_lower_from_int, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_upper_from_int, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_to_int_concat_neg_one, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_is_digit_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_leq_empty, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_leq_empty_eq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_leq_concat_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_leq_concat_true, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_leq_concat_base_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_leq_concat_base_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_lt_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_from_int_no_ctn_nondigit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_ctn_contra, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_ctn, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_dual_ctn, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_dual_ctn_false, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_self_ctn_simp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_replace_emp_ctn_src, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_char_start_eq_len, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_repl_char, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_repl_self_tgt_char, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_repl_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_contains_repl_tgt, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_len_id, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_src_tgt_no_ctn, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_tgt_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_tgt_no_ctn, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_src_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_src_inv_no_ctn1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_src_inv_no_ctn2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_src_inv_no_ctn3, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_dual_self, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_dual_ite1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_dual_ite2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_repl_repl_lookahead_id_simp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_all_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_opt_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_diff_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_plus_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_repeat_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_concat_star_swap, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_concat_star_repeat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_concat_star_nullable1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_concat_star_nullable2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_concat_merge, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_union_all, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_union_const_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_inter_all, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_star_none, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_star_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_star_star, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_range_refl, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_range_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_range_non_singleton_1, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_range_non_singleton_2, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_star_union_char, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_star_union_drop_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_loop_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_loop_star, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_inter_cstring, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_inter_cstring_neg, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_len_include, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_len_include_pre, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_substr_len_norm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_len_rev, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_rev_rev, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_rev_concat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_repl_self_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_repl_no_change, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_repl_tgt_eq_len, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_repl_len_one_emp_prefix, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_repl_emp_tgt_nemp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_repl_nemp_src_emp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_eq_repl_self_src, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_len_unit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_nth_unit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_nth_concat_unit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_nth_concat_unit_gen, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.seq_rev_unit, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_in_empty, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_in_sigma, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_in_sigma_star, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_in_cstring, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.re_in_comp, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_union_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_inter_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_range_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_contains, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_from_int_nemp_dig_range, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.str_in_re_from_int_dig_range, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.eq_refl, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.eq_symm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.eq_cond_deq, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.eq_ite_lift, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.distinct_binary_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_bv2nat_int2bv, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_bv2nat_int2bv_extend, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_bv2nat_int2bv_extract, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_int2bv_bv2nat, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_bv2nat_geq_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_int2bv_bvult_equiv, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_int2bv_bvule_equiv, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.uf_sbv_to_int_elim, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.evaluate, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.distinct_values, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.aci_norm, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.absorb, h => by
    simp [enc_CRule, dec_CRule]
  | Eo.CRule.distinct_card_conflict, h => by
    simp [enc_CRule, dec_CRule]
end

instance : Embedded Eo.CRule := ⟨enc_CRule, dec_CRule, emb_CRule, dec_enc_CRule⟩

@[simp] theorem embedded_enc_CRule (x : Eo.CRule) : Embedded.enc x = enc_CRule x := rfl
@[simp] theorem embedded_emb_CRule (x : Eo.CRule) : Embedded.emb x = emb_CRule x := rfl

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

theorem inv_SmtDatatype_null {x : Smtm.SmtDatatype} {ts : List Tree}
    (h : enc_SmtDatatype x = Tree.node schema.Constructor.eo__24emb_5fdt_2enull ts) :
    x = Smtm.SmtDatatype.null ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtDatatype]

theorem inv_SmtDatatype_sum {x : Smtm.SmtDatatype} {ts : List Tree}
    (h : enc_SmtDatatype x = Tree.node schema.Constructor.eo__24emb_5fdt_2esum ts) :
    ∃ x0 x1, x = Smtm.SmtDatatype.sum x0 x1 ∧ ts = [(enc_SmtDatatypeCons x0), (enc_SmtDatatype x1)] := by
  cases x <;> simp_all [enc_SmtDatatype]

theorem inv_SmtDatatypeCons_unit {x : Smtm.SmtDatatypeCons} {ts : List Tree}
    (h : enc_SmtDatatypeCons x = Tree.node schema.Constructor.eo__24emb_5fdtc_2eunit ts) :
    x = Smtm.SmtDatatypeCons.unit ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtDatatypeCons]

theorem inv_SmtDatatypeCons_cons {x : Smtm.SmtDatatypeCons} {ts : List Tree}
    (h : enc_SmtDatatypeCons x = Tree.node schema.Constructor.eo__24emb_5fdtc_2econs ts) :
    ∃ x0 x1, x = Smtm.SmtDatatypeCons.cons x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtDatatypeCons x1)] := by
  cases x <;> simp_all [enc_SmtDatatypeCons]

theorem inv_SmtDatatypeDecl_nil {x : Smtm.SmtDatatypeDecl} {ts : List Tree}
    (h : enc_SmtDatatypeDecl x = Tree.node schema.Constructor.eo__24emb_5fdd_2enil ts) :
    x = Smtm.SmtDatatypeDecl.nil ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtDatatypeDecl]

theorem inv_SmtDatatypeDecl_cons {x : Smtm.SmtDatatypeDecl} {ts : List Tree}
    (h : enc_SmtDatatypeDecl x = Tree.node schema.Constructor.eo__24emb_5fdd_2econs ts) :
    ∃ x0 x1 x2, x = Smtm.SmtDatatypeDecl.cons x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatype x1), (enc_SmtDatatypeDecl x2)] := by
  cases x <;> simp_all [enc_SmtDatatypeDecl]

theorem inv_SmtType_None {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eNone ts) :
    x = Smtm.SmtType.None ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Bool {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eBool ts) :
    x = Smtm.SmtType.Bool ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Int {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eInt ts) :
    x = Smtm.SmtType.Int ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Real {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eReal ts) :
    x = Smtm.SmtType.Real ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_RegLan {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eRegLan ts) :
    x = Smtm.SmtType.RegLan ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_BitVec {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eBitVec ts) :
    ∃ x0, x = Smtm.SmtType.BitVec x0 ∧ ts = [(Tree.encNat x0)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Map {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eMap ts) :
    ∃ x0 x1, x = Smtm.SmtType.Map x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtType x1)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Set {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eSet ts) :
    ∃ x0, x = Smtm.SmtType.Set x0 ∧ ts = [(enc_SmtType x0)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Seq {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eSeq ts) :
    ∃ x0, x = Smtm.SmtType.Seq x0 ∧ ts = [(enc_SmtType x0)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Char {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eChar ts) :
    x = Smtm.SmtType.Char ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_Datatype {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eDatatype ts) :
    ∃ x0 x1, x = Smtm.SmtType.Datatype x0 x1 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_TypeRef {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eTypeRef ts) :
    ∃ x0, x = Smtm.SmtType.TypeRef x0 ∧ ts = [(Tree.encStr x0)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_USort {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eUSort ts) :
    ∃ x0, x = Smtm.SmtType.USort x0 ∧ ts = [(Tree.encNat x0)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_FunType {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eFunType ts) :
    ∃ x0 x1, x = Smtm.SmtType.FunType x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtType x1)] := by
  cases x <;> simp_all [enc_SmtType]

theorem inv_SmtType_DtcAppType {x : Smtm.SmtType} {ts : List Tree}
    (h : enc_SmtType x = Tree.node schema.Constructor.eo__24emb_5ftsm_2eDtcAppType ts) :
    ∃ x0 x1, x = Smtm.SmtType.DtcAppType x0 x1 ∧ ts = [(enc_SmtType x0), (enc_SmtType x1)] := by
  cases x <;> simp_all [enc_SmtType]

mutual
theorem dec_enc_SmtDatatype : (x : Smtm.SmtDatatype) → emb_SmtDatatype x → dec_SmtDatatype (enc_SmtDatatype x) = some x
  | Smtm.SmtDatatype.null, h => by
    simp [enc_SmtDatatype, dec_SmtDatatype]
  | Smtm.SmtDatatype.sum x0 x1, h => by
    simp only [emb_SmtDatatype] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtDatatype, dec_SmtDatatype, dec_enc_SmtDatatypeCons x0 h0, dec_enc_SmtDatatype x1 h1]
theorem dec_enc_SmtDatatypeCons : (x : Smtm.SmtDatatypeCons) → emb_SmtDatatypeCons x → dec_SmtDatatypeCons (enc_SmtDatatypeCons x) = some x
  | Smtm.SmtDatatypeCons.unit, h => by
    simp [enc_SmtDatatypeCons, dec_SmtDatatypeCons]
  | Smtm.SmtDatatypeCons.cons x0 x1, h => by
    simp only [emb_SmtDatatypeCons] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtDatatypeCons, dec_SmtDatatypeCons, dec_enc_SmtType x0 h0, dec_enc_SmtDatatypeCons x1 h1]
theorem dec_enc_SmtDatatypeDecl : (x : Smtm.SmtDatatypeDecl) → emb_SmtDatatypeDecl x → dec_SmtDatatypeDecl (enc_SmtDatatypeDecl x) = some x
  | Smtm.SmtDatatypeDecl.nil, h => by
    simp [enc_SmtDatatypeDecl, dec_SmtDatatypeDecl]
  | Smtm.SmtDatatypeDecl.cons x0 x1 x2, h => by
    simp only [emb_SmtDatatypeDecl] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtDatatypeDecl, dec_SmtDatatypeDecl, Tree.dec_encStr x0 h0, dec_enc_SmtDatatype x1 h1, dec_enc_SmtDatatypeDecl x2 h2]
theorem dec_enc_SmtType : (x : Smtm.SmtType) → emb_SmtType x → dec_SmtType (enc_SmtType x) = some x
  | Smtm.SmtType.None, h => by
    simp [enc_SmtType, dec_SmtType]
  | Smtm.SmtType.Bool, h => by
    simp [enc_SmtType, dec_SmtType]
  | Smtm.SmtType.Int, h => by
    simp [enc_SmtType, dec_SmtType]
  | Smtm.SmtType.Real, h => by
    simp [enc_SmtType, dec_SmtType]
  | Smtm.SmtType.RegLan, h => by
    simp [enc_SmtType, dec_SmtType]
  | Smtm.SmtType.BitVec x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp [enc_SmtType, dec_SmtType, Tree.dec_encNat x0 h0]
  | Smtm.SmtType.Map x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtType, dec_SmtType, dec_enc_SmtType x0 h0, dec_enc_SmtType x1 h1]
  | Smtm.SmtType.Set x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp [enc_SmtType, dec_SmtType, dec_enc_SmtType x0 h0]
  | Smtm.SmtType.Seq x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp [enc_SmtType, dec_SmtType, dec_enc_SmtType x0 h0]
  | Smtm.SmtType.Char, h => by
    simp [enc_SmtType, dec_SmtType]
  | Smtm.SmtType.Datatype x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtType, dec_SmtType, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1]
  | Smtm.SmtType.TypeRef x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp [enc_SmtType, dec_SmtType, Tree.dec_encStr x0 h0]
  | Smtm.SmtType.USort x0, h => by
    simp only [emb_SmtType] at h
    have h0 := h
    simp [enc_SmtType, dec_SmtType, Tree.dec_encNat x0 h0]
  | Smtm.SmtType.FunType x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtType, dec_SmtType, dec_enc_SmtType x0 h0, dec_enc_SmtType x1 h1]
  | Smtm.SmtType.DtcAppType x0 x1, h => by
    simp only [emb_SmtType] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtType, dec_SmtType, dec_enc_SmtType x0 h0, dec_enc_SmtType x1 h1]
end

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

theorem inv_SmtBindings_nil {x : Smtm.SmtBindings} {ts : List Tree}
    (h : enc_SmtBindings x = Tree.node schema.Constructor.eo__24emb_5fsbd_2enil ts) :
    x = Smtm.SmtBindings.nil ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtBindings]

theorem inv_SmtBindings_cons {x : Smtm.SmtBindings} {ts : List Tree}
    (h : enc_SmtBindings x = Tree.node schema.Constructor.eo__24emb_5fsbd_2econs ts) :
    ∃ x0 x1 x2 x3, x = Smtm.SmtBindings.cons x0 x1 x2 x3 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2), (enc_SmtBindings x3)] := by
  cases x <;> simp_all [enc_SmtBindings]

theorem inv_SmtTerm_None {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eNone ts) :
    x = Smtm.SmtTerm.None ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_Boolean {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eBoolean ts) :
    ∃ x0, x = Smtm.SmtTerm.Boolean x0 ∧ ts = [(Tree.encBool x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_Numeral {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eNumeral ts) :
    ∃ x0, x = Smtm.SmtTerm.Numeral x0 ∧ ts = [(Tree.encInt x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_Rational {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eRational ts) :
    ∃ x0, x = Smtm.SmtTerm.Rational x0 ∧ ts = [(Tree.encRat x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_String {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eString ts) :
    ∃ x0, x = Smtm.SmtTerm.String x0 ∧ ts = [(Tree.encStr x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_Binary {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eBinary ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.Binary x0 x1 ∧ ts = [(Tree.encInt x0), (Tree.encInt x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_Apply {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eApply ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.Apply x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_Var {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eVar ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.Var x0 x1 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_DtCons {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eDtCons ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.DtCons x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_DtSel {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eDtSel ts) :
    ∃ x0 x1 x2 x3, x = Smtm.SmtTerm.DtSel x0 x1 x2 x3 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2), (Tree.encNat x3)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_DtTester {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eDtTester ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.DtTester x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtDatatypeDecl x1), (Tree.encNat x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_UConst {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eUConst ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.UConst x0 x1 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_ite {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eite ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.ite x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_not {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2enot ts) :
    ∃ x0, x = Smtm.SmtTerm.not x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_or {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eor ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.or x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_and {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eand ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.and x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_imp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d_3e ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.imp x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_xor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2exor ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.xor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_eq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3d ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.eq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_lam {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2elam ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.lam x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bind {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebind ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bind x0 x1 ∧ ts = [(enc_SmtBindings x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm__at_purify {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_40purify ts) :
    ∃ x0, x = Smtm.SmtTerm._at_purify x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_plus {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2b ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.plus x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_neg {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2d ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.neg x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_mult {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2a ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.mult x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_lt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.lt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_leq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3c_3d ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.leq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_gt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.gt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_geq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_3e_3d ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.geq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_to_real {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5freal ts) :
    ∃ x0, x = Smtm.SmtTerm.to_real x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eto_5fint ts) :
    ∃ x0, x = Smtm.SmtTerm.to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_is_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eis_5fint ts) :
    ∃ x0, x = Smtm.SmtTerm.is_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_abs {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eabs ts) :
    ∃ x0, x = Smtm.SmtTerm.abs x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_uneg {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2euneg ts) :
    ∃ x0, x = Smtm.SmtTerm.uneg x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_div {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ediv ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.div x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_mod {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2emod ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.mod x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_divisible {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2edivisible ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.divisible x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_int_pow2 {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2epow2 ts) :
    ∃ x0, x = Smtm.SmtTerm.int_pow2 x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_int_log2 {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eint_2elog2 ts) :
    ∃ x0, x = Smtm.SmtTerm.int_log2 x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_div_total {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.div_total x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_mod_total {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2emod_5ftotal ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.mod_total x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_select {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eselect ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.select x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_store {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estore ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.store x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_map_diff {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2emap_5fdiff ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.map_diff x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_concat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2econcat ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.concat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_extract {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eextract ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.extract x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_repeat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2erepeat ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.repeat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvnot {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnot ts) :
    ∃ x0, x = Smtm.SmtTerm.bvnot x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvand {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvand ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvand x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvor ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvnand {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnand ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvnand x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvnor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnor ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvnor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvxor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxor ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvxor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvxnor {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvxnor ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvxnor x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvcomp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvcomp ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvcomp x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvneg {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvneg ts) :
    ∃ x0, x = Smtm.SmtTerm.bvneg x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvadd {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvadd ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvadd x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvmul {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvmul ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvmul x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvudiv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvudiv ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvudiv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvurem {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvurem ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvurem x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsub {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsub ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsub x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsdiv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdiv ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsdiv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsrem {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsrem ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsrem x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsmod {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmod ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsmod x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvult {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvult ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvult x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvule {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvule ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvule x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvugt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvugt ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvugt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvuge {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuge ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvuge x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvslt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvslt ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvslt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsle {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsle ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsle x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsgt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsgt ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsgt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsge {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsge ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsge x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvshl {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvshl ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvshl x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvlshr {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvlshr ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvlshr x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvashr {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvashr ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvashr x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_zero_extend {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ezero_5fextend ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.zero_extend x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_sign_extend {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2esign_5fextend ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.sign_extend x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_rotate_left {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fleft ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.rotate_left x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_rotate_right {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2erotate_5fright ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.rotate_right x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvuaddo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvuaddo ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvuaddo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvnego {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvnego ts) :
    ∃ x0, x = Smtm.SmtTerm.bvnego x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsaddo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsaddo ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsaddo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvumulo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvumulo ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvumulo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsmulo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsmulo ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsmulo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvusubo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvusubo ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvusubo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvssubo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvssubo ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvssubo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_bvsdivo {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ebvsdivo ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.bvsdivo x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_seq_empty {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eempty ts) :
    ∃ x0, x = Smtm.SmtTerm.seq_empty x0 ∧ ts = [(enc_SmtType x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_len {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2elen ts) :
    ∃ x0, x = Smtm.SmtTerm.str_len x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_concat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_concat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_substr {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esubstr ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_substr x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_contains {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2econtains ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_contains x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_replace {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_indexof {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_indexof x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_at {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eat ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_at x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_prefixof {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_prefixof x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_suffixof {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_suffixof x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_rev {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2erev ts) :
    ∃ x0, x = Smtm.SmtTerm.str_rev x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_update {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eupdate ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_update x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_to_lower {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower ts) :
    ∃ x0, x = Smtm.SmtTerm.str_to_lower x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_to_upper {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper ts) :
    ∃ x0, x = Smtm.SmtTerm.str_to_upper x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_to_code {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode ts) :
    ∃ x0, x = Smtm.SmtTerm.str_to_code x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_from_code {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode ts) :
    ∃ x0, x = Smtm.SmtTerm.str_from_code x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_is_digit {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit ts) :
    ∃ x0, x = Smtm.SmtTerm.str_is_digit x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint ts) :
    ∃ x0, x = Smtm.SmtTerm.str_to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_from_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint ts) :
    ∃ x0, x = Smtm.SmtTerm.str_from_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_lt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_lt x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_leq {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_leq x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_replace_all {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace_all x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_replace_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace_re x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_replace_re_all {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_replace_re_all x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_indexof_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_indexof_re x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_allchar {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eallchar ts) :
    x = Smtm.SmtTerm.re_allchar ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_none {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2enone ts) :
    x = Smtm.SmtTerm.re_none ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_all {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eall ts) :
    x = Smtm.SmtTerm.re_all ∧ ts = [] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_to_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre ts) :
    ∃ x0, x = Smtm.SmtTerm.str_to_re x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_mult {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2a ts) :
    ∃ x0, x = Smtm.SmtTerm.re_mult x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_plus {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b ts) :
    ∃ x0, x = Smtm.SmtTerm.re_plus x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_exp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_5e ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_exp x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_opt {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eopt ts) :
    ∃ x0, x = Smtm.SmtTerm.re_opt x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_comp {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ecomp ts) :
    ∃ x0, x = Smtm.SmtTerm.re_comp x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_range {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2erange ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_range x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_concat {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_concat x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_inter {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2einter ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_inter x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_union {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eunion ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_union x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_diff {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2ediff ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.re_diff x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_re_loop {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2ere_2eloop ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.re_loop x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_in_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.str_in_re x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_seq_unit {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2eunit ts) :
    ∃ x0, x = Smtm.SmtTerm.seq_unit x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_seq_nth {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_2enth ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.seq_nth x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_str_indexof_re_split {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.str_indexof_re_split x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_seq_diff {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.seq_diff x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm__at_strings_occur_index {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm._at_strings_occur_index x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm__at_strings_occur_index_re {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_choice {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2echoice ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.choice x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_set_empty {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eempty ts) :
    ∃ x0, x = Smtm.SmtTerm.set_empty x0 ∧ ts = [(enc_SmtType x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_set_singleton {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esingleton ts) :
    ∃ x0, x = Smtm.SmtTerm.set_singleton x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_set_union {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eunion ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_union x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_set_inter {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2einter ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_inter x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_set_minus {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2eminus ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_minus x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_set_member {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2emember ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_member x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_set_subset {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eset_2esubset ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.set_subset x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_qdiv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.qdiv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_qdiv_total {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.qdiv_total x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_forall {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eforall ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.forall x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_exists {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eexists ts) :
    ∃ x0 x1 x2, x = Smtm.SmtTerm.exists x0 x1 x2 ∧ ts = [(Tree.encStr x0), (enc_SmtType x1), (enc_SmtTerm x2)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_int_to_bv {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv ts) :
    ∃ x0 x1, x = Smtm.SmtTerm.int_to_bv x0 x1 ∧ ts = [(enc_SmtTerm x0), (enc_SmtTerm x1)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_ubv_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint ts) :
    ∃ x0, x = Smtm.SmtTerm.ubv_to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

theorem inv_SmtTerm_sbv_to_int {x : Smtm.SmtTerm} {ts : List Tree}
    (h : enc_SmtTerm x = Tree.node schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint ts) :
    ∃ x0, x = Smtm.SmtTerm.sbv_to_int x0 ∧ ts = [(enc_SmtTerm x0)] := by
  cases x <;> simp_all [enc_SmtTerm]

mutual
theorem dec_enc_SmtBindings : (x : Smtm.SmtBindings) → emb_SmtBindings x → dec_SmtBindings (enc_SmtBindings x) = some x
  | Smtm.SmtBindings.nil, h => by
    simp [enc_SmtBindings, dec_SmtBindings]
  | Smtm.SmtBindings.cons x0 x1 x2 x3, h => by
    simp only [emb_SmtBindings] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp [enc_SmtBindings, dec_SmtBindings, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2, dec_enc_SmtBindings x3 h3]
theorem dec_enc_SmtTerm : (x : Smtm.SmtTerm) → emb_SmtTerm x → dec_SmtTerm (enc_SmtTerm x) = some x
  | Smtm.SmtTerm.None, h => by
    simp [enc_SmtTerm, dec_SmtTerm]
  | Smtm.SmtTerm.Boolean x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encBool x0 h0]
  | Smtm.SmtTerm.Numeral x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encInt x0 h0]
  | Smtm.SmtTerm.Rational x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encRat x0 h0]
  | Smtm.SmtTerm.String x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0]
  | Smtm.SmtTerm.Binary x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encInt x0 h0, Tree.dec_encInt x1 h1]
  | Smtm.SmtTerm.Apply x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.Var x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1]
  | Smtm.SmtTerm.DtCons x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1, Tree.dec_encNat x2 h2]
  | Smtm.SmtTerm.DtSel x0 x1 x2 x3, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1, Tree.dec_encNat x2 h2, Tree.dec_encNat x3 h3]
  | Smtm.SmtTerm.DtTester x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtDatatypeDecl x1 h1, Tree.dec_encNat x2 h2]
  | Smtm.SmtTerm.UConst x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1]
  | Smtm.SmtTerm.ite x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.not x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.or x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.and x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.imp x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.xor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.eq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.lam x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.bind x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtBindings x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm._at_purify x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.plus x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.neg x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.mult x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.lt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.leq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.gt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.geq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.to_real x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.is_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.abs x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.uneg x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.div x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.mod x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.divisible x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.int_pow2 x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.int_log2 x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.div_total x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.mod_total x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.select x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.store x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.map_diff x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.concat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.extract x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.repeat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvnot x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.bvand x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvnand x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvnor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvxor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvxnor x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvcomp x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvneg x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.bvadd x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvmul x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvudiv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvurem x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsub x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsdiv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsrem x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsmod x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvult x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvule x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvugt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvuge x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvslt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsle x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsgt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsge x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvshl x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvlshr x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvashr x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.zero_extend x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.sign_extend x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.rotate_left x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.rotate_right x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvuaddo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvnego x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.bvsaddo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvumulo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsmulo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvusubo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvssubo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.bvsdivo x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.seq_empty x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtType x0 h0]
  | Smtm.SmtTerm.str_len x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_concat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_substr x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_contains x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_replace x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_indexof x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_at x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_prefixof x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_suffixof x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_rev x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_update x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_to_lower x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_to_upper x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_to_code x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_from_code x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_is_digit x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_from_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.str_lt x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_leq x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_replace_all x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_replace_re x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_replace_re_all x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_indexof_re x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.re_allchar, h => by
    simp [enc_SmtTerm, dec_SmtTerm]
  | Smtm.SmtTerm.re_none, h => by
    simp [enc_SmtTerm, dec_SmtTerm]
  | Smtm.SmtTerm.re_all, h => by
    simp [enc_SmtTerm, dec_SmtTerm]
  | Smtm.SmtTerm.str_to_re x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.re_mult x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.re_plus x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.re_exp x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.re_opt x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.re_comp x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.re_range x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.re_concat x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.re_inter x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.re_union x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.re_diff x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.re_loop x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.str_in_re x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.seq_unit x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.seq_nth x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.str_indexof_re_split x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.seq_diff x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm._at_strings_occur_index x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.choice x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.set_empty x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtType x0 h0]
  | Smtm.SmtTerm.set_singleton x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.set_union x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.set_inter x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.set_minus x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.set_member x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.set_subset x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.qdiv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.qdiv_total x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.forall x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.exists x0 x1 x2, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, Tree.dec_encStr x0 h0, dec_enc_SmtType x1 h1, dec_enc_SmtTerm x2 h2]
  | Smtm.SmtTerm.int_to_bv x0 x1, h => by
    simp only [emb_SmtTerm] at h
    obtain ⟨h0, h1⟩ := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0, dec_enc_SmtTerm x1 h1]
  | Smtm.SmtTerm.ubv_to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
  | Smtm.SmtTerm.sbv_to_int x0, h => by
    simp only [emb_SmtTerm] at h
    have h0 := h
    simp [enc_SmtTerm, dec_SmtTerm, dec_enc_SmtTerm x0 h0]
end

instance : Embedded Smtm.SmtBindings := ⟨enc_SmtBindings, dec_SmtBindings, emb_SmtBindings, dec_enc_SmtBindings⟩

@[simp] theorem embedded_enc_SmtBindings (x : Smtm.SmtBindings) : Embedded.enc x = enc_SmtBindings x := rfl
@[simp] theorem embedded_emb_SmtBindings (x : Smtm.SmtBindings) : Embedded.emb x = emb_SmtBindings x := rfl

instance : Embedded Smtm.SmtTerm := ⟨enc_SmtTerm, dec_SmtTerm, emb_SmtTerm, dec_enc_SmtTerm⟩

@[simp] theorem embedded_enc_SmtTerm (x : Smtm.SmtTerm) : Embedded.enc x = enc_SmtTerm x := rfl
@[simp] theorem embedded_emb_SmtTerm (x : Smtm.SmtTerm) : Embedded.emb x = emb_SmtTerm x := rfl


end

end pathos_compiled_checker.Embed
