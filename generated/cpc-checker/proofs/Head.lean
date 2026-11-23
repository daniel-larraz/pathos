module
public import $CHECKER$
public import $CALC$.Logos
import all $CALC$.Logos
public import $CALC$.SmtTranslate
import all $CALC$.SmtTranslate
public import $CALC$.SmtModel
import all $CALC$.SmtModel
public import $CASES$
import all $CASES$
public import PathosProofs.Generated

/-!
# The proofs about the generated functions

Written by Ethos's rust-meta with the functions: for each program, that its
Rust computes what logos's function of the same name does. Do not edit.
-/

set_option linter.unusedVariables false
set_option maxRecDepth 8000

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result
open Eo hiding Term
open Smtm
open generated generated.part0 generated.part1 generated.part2 generated.part3 generated.part4 generated.part5 generated.part6 generated.part7 generated.part8 generated.part9 generated.part10 generated.part11 generated.part12

/-- What is proved of `$arith_normalize_lit`. -/
def eo__24arith_5fnormalize_5flit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_normalize_lit x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$arith_rel_inv`. -/
def eo__24arith_5frel_5finv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_inv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$arith_rel_neg`. -/
def eo__24arith_5frel_5fneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_neg x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$arith_rel_sum`. -/
def eo__24arith_5frel_5fsum.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_sum x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$arith_rel_trichotomy`. -/
def eo__24arith_5frel_5ftrichotomy.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_trichotomy x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_binary_app`. -/
def eo__24bv_5fbitblast_5fbinary_5fapp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_binary_app x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_head`. -/
def eo__24bv_5fbitblast_5fhead.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fbitblast_5fhead s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_head x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_tail`. -/
def eo__24bv_5fbitblast_5ftail.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fbitblast_5ftail s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_tail x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitwidth`. -/
def eo__24bv_5fbitwidth.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fbitwidth s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitwidth x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$dt_arg_list`. -/
def eo__24dt_5farg_5flist.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_arg_list x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_StateObj_proven`. -/
def eo__24eo_5fStateObj_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_StateObj_proven x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_cmd_step_pop_proven`. -/
def eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → StateOK x_a0 →
    eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_dd_lookup`. -/
def eo__24eo_5fdd_5flookup.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_lookup x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_dd_resolve`. -/
def eo__24eo_5fdd_5fresolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fdd_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_disamb_type_seq.empty`. -/
def eo__24eo_5fdisamb_5ftype_5fseq_2eempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fdisamb_5ftype_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_disamb_type_seq_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_disamb_type_set.empty`. -/
def eo__24eo_5fdisamb_5ftype_5fset_2eempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fdisamb_5ftype_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_disamb_type_set_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_dt_resolve`. -/
def eo__24eo_5fdt_5fresolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_dtc_resolve`. -/
def eo__24eo_5fdtc_5fresolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dtc_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_invoke_cmd_check_proven`. -/
def eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
    eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_@@TypedList.cons`. -/
def eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil__at__at_TypedList_cons x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_lit_type_Binary`. -/
def eo__24eo_5flit_5ftype_5fBinary.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5flit_5ftype_5fBinary s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Binary x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_lit_type_Numeral`. -/
def eo__24eo_5flit_5ftype_5fNumeral.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5flit_5ftype_5fNumeral s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Numeral x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_lit_type_Rational`. -/
def eo__24eo_5flit_5ftype_5fRational.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5flit_5ftype_5fRational s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Rational x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_lit_type_String`. -/
def eo__24eo_5flit_5ftype_5fString.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5flit_5ftype_5fString s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_String x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_@@TypedList.cons`. -/
def eo__24eo_5fnil_5f_40_40TypedList_2econs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil__at__at_TypedList_cons x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_and_intro`. -/
def eo__24eo_5fprog_5fand_5fintro.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fand_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_and_intro x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-abs-eq`. -/
def eo__24eo_5fprog_5farith_2dabs_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dabs_2deq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_abs_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-div-int-to-real`. -/
def eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_div_int_to_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-div-total-int-to-real`. -/
def eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_div_total_int_to_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-elim-gt`. -/
def eo__24eo_5fprog_5farith_2delim_2dgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2delim_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_gt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-elim-leq`. -/
def eo__24eo_5fprog_5farith_2delim_2dleq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2delim_2dleq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_leq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-elim-lt`. -/
def eo__24eo_5fprog_5farith_2delim_2dlt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2delim_2dlt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_lt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-eq-elim-int`. -/
def eo__24eo_5fprog_5farith_2deq_2delim_2dint.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2deq_2delim_2dint s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_eq_elim_int x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-eq-elim-real`. -/
def eo__24eo_5fprog_5farith_2deq_2delim_2dreal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2deq_2delim_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_eq_elim_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-geq-ite-lift`. -/
def eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_geq_ite_lift x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-eq-conflict`. -/
def eo__24eo_5fprog_5farith_2dint_2deq_2dconflict.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2dint_2deq_2dconflict s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_eq_conflict x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-is-int-elim-to-real`. -/
def eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_is_int_elim_to_real x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-leq-ite-lift`. -/
def eo__24eo_5fprog_5farith_2dleq_2dite_2dlift.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5farith_2dleq_2dite_2dlift s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_leq_ite_lift x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-max-geq1`. -/
def eo__24eo_5fprog_5farith_2dmax_2dgeq1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dmax_2dgeq1 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_max_geq1 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-max-geq2`. -/
def eo__24eo_5fprog_5farith_2dmax_2dgeq2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dmax_2dgeq2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_max_geq2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-min-lt1`. -/
def eo__24eo_5fprog_5farith_2dmin_2dlt1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dmin_2dlt1 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_min_lt1 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-min-lt2`. -/
def eo__24eo_5fprog_5farith_2dmin_2dlt2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dmin_2dlt2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_min_lt2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-to-int-elim-to-real`. -/
def eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_to_int_elim_to_real x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith_trichotomy`. -/
def eo__24eo_5fprog_5farith_5ftrichotomy.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → ProofOK x_a0 → ProofOK x_a1 →
    eo__24eo_5fprog_5farith_5ftrichotomy s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_trichotomy x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_array-read-over-write`. -/
def eo__24eo_5fprog_5farray_2dread_2dover_2dwrite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farray_2dread_2dover_2dwrite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_array_read_over_write x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_array-read-over-write-split`. -/
def eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_array_read_over_write_split x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_array-read-over-write2`. -/
def eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_array_read_over_write2 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_array-store-overwrite`. -/
def eo__24eo_5fprog_5farray_2dstore_2doverwrite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5farray_2dstore_2doverwrite s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_array_store_overwrite x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_array-store-self`. -/
def eo__24eo_5fprog_5farray_2dstore_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farray_2dstore_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_array_store_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_array-store-swap`. -/
def eo__24eo_5fprog_5farray_2dstore_2dswap.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5farray_2dstore_2dswap s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_array_store_swap x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arrays_ext`. -/
def eo__24eo_5fprog_5farrays_5fext.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farrays_5fext s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arrays_ext x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arrays_read_over_write`. -/
def eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arrays_read_over_write x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arrays_read_over_write_1`. -/
def eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arrays_read_over_write_1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-double-not-elim`. -/
def eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_double_not_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-dual-impl-eq`. -/
def eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_dual_impl_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-eq-false`. -/
def eo__24eo_5fprog_5fbool_2deq_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2deq_2dfalse s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_eq_false x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-eq-nrefl`. -/
def eo__24eo_5fprog_5fbool_2deq_2dnrefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2deq_2dnrefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_eq_nrefl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-eq-true`. -/
def eo__24eo_5fprog_5fbool_2deq_2dtrue.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2deq_2dtrue s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_eq_true x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-impl-elim`. -/
def eo__24eo_5fprog_5fbool_2dimpl_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dimpl_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_impl_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-impl-false1`. -/
def eo__24eo_5fprog_5fbool_2dimpl_2dfalse1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dimpl_2dfalse1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_impl_false1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-impl-false2`. -/
def eo__24eo_5fprog_5fbool_2dimpl_2dfalse2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dimpl_2dfalse2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_impl_false2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-impl-true1`. -/
def eo__24eo_5fprog_5fbool_2dimpl_2dtrue1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dimpl_2dtrue1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_impl_true1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-impl-true2`. -/
def eo__24eo_5fprog_5fbool_2dimpl_2dtrue2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dimpl_2dtrue2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_impl_true2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-implies-de-morgan`. -/
def eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_implies_de_morgan x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-not-eq-elim1`. -/
def eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_not_eq_elim1 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-not-eq-elim2`. -/
def eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_not_eq_elim2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-not-false`. -/
def eo__24eo_5fprog_5fbool_2dnot_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dnot_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_not_false x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-not-ite-elim`. -/
def eo__24eo_5fprog_5fbool_2dnot_2dite_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbool_2dnot_2dite_2delim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_not_ite_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-not-true`. -/
def eo__24eo_5fprog_5fbool_2dnot_2dtrue.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dnot_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_not_true x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-not-xor-elim`. -/
def eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_not_xor_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-xor-comm`. -/
def eo__24eo_5fprog_5fbool_2dxor_2dcomm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dxor_2dcomm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_xor_comm x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-xor-elim`. -/
def eo__24eo_5fprog_5fbool_2dxor_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbool_2dxor_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_xor_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-xor-false`. -/
def eo__24eo_5fprog_5fbool_2dxor_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dxor_2dfalse s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_xor_false x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-xor-nrefl`. -/
def eo__24eo_5fprog_5fbool_2dxor_2dnrefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dxor_2dnrefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_xor_nrefl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-xor-refl`. -/
def eo__24eo_5fprog_5fbool_2dxor_2drefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dxor_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_xor_refl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-xor-true`. -/
def eo__24eo_5fprog_5fbool_2dxor_2dtrue.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbool_2dxor_2dtrue s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_xor_true x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-commutative-comp`. -/
def eo__24eo_5fprog_5fbv_2dcommutative_2dcomp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dcommutative_2dcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_commutative_comp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-eq-not-solve`. -/
def eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_eq_not_solve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-extract-not`. -/
def eo__24eo_5fprog_5fbv_2dextract_2dnot.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2dextract_2dnot s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_not x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-extract-sign-extend-1`. -/
def eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_sign_extend_1 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-equal-children`. -/
def eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_children x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-equal-cond-1`. -/
def eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-equal-cond-2`. -/
def eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-equal-cond-3`. -/
def eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_3 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-lt-self`. -/
def eo__24eo_5fprog_5fbv_2dlt_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dlt_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lt_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-not-idemp`. -/
def eo__24eo_5fprog_5fbv_2dnot_2didemp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dnot_2didemp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_idemp x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-not-ult`. -/
def eo__24eo_5fprog_5fbv_2dnot_2dult.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dnot_2dult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_ult x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-not-xor`. -/
def eo__24eo_5fprog_5fbv_2dnot_2dxor.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2dnot_2dxor s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_xor x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-sge-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dsge_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dsge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sge_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-sgt-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dsgt_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dsgt_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sgt_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-sle-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dsle_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dsle_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sle_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-sle-self`. -/
def eo__24eo_5fprog_5fbv_2dsle_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dsle_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sle_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-uge-eliminate`. -/
def eo__24eo_5fprog_5fbv_2duge_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2duge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_uge_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ugt-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dugt_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dugt_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ugt_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ule-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dule_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dule_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ule-self`. -/
def eo__24eo_5fprog_5fbv_2dule_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dule_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ult-self`. -/
def eo__24eo_5fprog_5fbv_2dult_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dult_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ult_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_and_neg`. -/
def eo__24eo_5fprog_5fcnf_5fand_5fneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fand_5fneg s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_and_neg x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_equiv_neg1`. -/
def eo__24eo_5fprog_5fcnf_5fequiv_5fneg1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fequiv_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_equiv_neg1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_equiv_neg2`. -/
def eo__24eo_5fprog_5fcnf_5fequiv_5fneg2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fequiv_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_equiv_neg2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_equiv_pos1`. -/
def eo__24eo_5fprog_5fcnf_5fequiv_5fpos1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fequiv_5fpos1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_equiv_pos1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_equiv_pos2`. -/
def eo__24eo_5fprog_5fcnf_5fequiv_5fpos2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fequiv_5fpos2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_equiv_pos2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_implies_neg1`. -/
def eo__24eo_5fprog_5fcnf_5fimplies_5fneg1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fimplies_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_implies_neg1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_implies_neg2`. -/
def eo__24eo_5fprog_5fcnf_5fimplies_5fneg2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fimplies_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_implies_neg2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_implies_pos`. -/
def eo__24eo_5fprog_5fcnf_5fimplies_5fpos.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fimplies_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_implies_pos x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_ite_neg1`. -/
def eo__24eo_5fprog_5fcnf_5fite_5fneg1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fite_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_neg1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_ite_neg2`. -/
def eo__24eo_5fprog_5fcnf_5fite_5fneg2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fite_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_neg2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_ite_neg3`. -/
def eo__24eo_5fprog_5fcnf_5fite_5fneg3.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fite_5fneg3 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_neg3 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_ite_pos1`. -/
def eo__24eo_5fprog_5fcnf_5fite_5fpos1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fite_5fpos1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_pos1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_ite_pos2`. -/
def eo__24eo_5fprog_5fcnf_5fite_5fpos2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fite_5fpos2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_pos2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_ite_pos3`. -/
def eo__24eo_5fprog_5fcnf_5fite_5fpos3.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fite_5fpos3 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_pos3 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_or_pos`. -/
def eo__24eo_5fprog_5fcnf_5for_5fpos.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5for_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_or_pos x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_xor_neg1`. -/
def eo__24eo_5fprog_5fcnf_5fxor_5fneg1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fxor_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_neg1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_xor_neg2`. -/
def eo__24eo_5fprog_5fcnf_5fxor_5fneg2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fxor_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_neg2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_xor_pos1`. -/
def eo__24eo_5fprog_5fcnf_5fxor_5fpos1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fxor_5fpos1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_pos1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_xor_pos2`. -/
def eo__24eo_5fprog_5fcnf_5fxor_5fpos2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fxor_5fpos2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_pos2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_contra`. -/
def eo__24eo_5fprog_5fcontra.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_contra x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_eq-cond-deq`. -/
def eo__24eo_5fprog_5feq_2dcond_2ddeq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5feq_2dcond_2ddeq s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_cond_deq x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_eq-ite-lift`. -/
def eo__24eo_5fprog_5feq_2dite_2dlift.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5feq_2dite_2dlift s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_ite_lift x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_eq-refl`. -/
def eo__24eo_5fprog_5feq_2drefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5feq_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_refl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_eq-symm`. -/
def eo__24eo_5fprog_5feq_2dsymm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5feq_2dsymm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_symm x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_eq_resolve`. -/
def eo__24eo_5fprog_5feq_5fresolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5feq_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_equiv_elim1`. -/
def eo__24eo_5fprog_5fequiv_5felim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_equiv_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_equiv_elim2`. -/
def eo__24eo_5fprog_5fequiv_5felim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_equiv_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_exists-elim`. -/
def eo__24eo_5fprog_5fexists_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fexists_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_exists_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_false_elim`. -/
def eo__24eo_5fprog_5ffalse_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5ffalse_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_false_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_false_intro`. -/
def eo__24eo_5fprog_5ffalse_5fintro.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5ffalse_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_false_intro x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ho_cong`. -/
def eo__24eo_5fprog_5fho_5fcong.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fho_5fcong s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ho_cong x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_implies_elim`. -/
def eo__24eo_5fprog_5fimplies_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fimplies_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_implies_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-else-false`. -/
def eo__24eo_5fprog_5fite_2delse_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2delse_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_false x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-else-lookahead`. -/
def eo__24eo_5fprog_5fite_2delse_2dlookahead.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fite_2delse_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-else-lookahead-not-self`. -/
def eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_lookahead_not_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-else-lookahead-self`. -/
def eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_lookahead_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-else-neg-lookahead`. -/
def eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_neg_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-else-true`. -/
def eo__24eo_5fprog_5fite_2delse_2dtrue.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2delse_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_true x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-eq-branch`. -/
def eo__24eo_5fprog_5fite_2deq_2dbranch.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2deq_2dbranch s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_eq_branch x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-expand`. -/
def eo__24eo_5fprog_5fite_2dexpand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fite_2dexpand s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_expand x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-false-cond`. -/
def eo__24eo_5fprog_5fite_2dfalse_2dcond.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2dfalse_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_false_cond x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-neg-branch`. -/
def eo__24eo_5fprog_5fite_2dneg_2dbranch.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fite_2dneg_2dbranch s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_neg_branch x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-not-cond`. -/
def eo__24eo_5fprog_5fite_2dnot_2dcond.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fite_2dnot_2dcond s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_not_cond x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-then-false`. -/
def eo__24eo_5fprog_5fite_2dthen_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2dthen_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_false x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-then-lookahead`. -/
def eo__24eo_5fprog_5fite_2dthen_2dlookahead.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fite_2dthen_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-then-lookahead-not-self`. -/
def eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead_not_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-then-lookahead-self`. -/
def eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-then-neg-lookahead`. -/
def eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_neg_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-then-true`. -/
def eo__24eo_5fprog_5fite_2dthen_2dtrue.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2dthen_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_true x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite-true-cond`. -/
def eo__24eo_5fprog_5fite_2dtrue_2dcond.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fite_2dtrue_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_true_cond x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite_elim1`. -/
def eo__24eo_5fprog_5fite_5felim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite_elim2`. -/
def eo__24eo_5fprog_5fite_5felim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_ite_eq`. -/
def eo__24eo_5fprog_5fite_5feq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fite_5feq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_eq x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_modus_ponens`. -/
def eo__24eo_5fprog_5fmodus_5fponens.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fmodus_5fponens s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_modus_ponens x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_and`. -/
def eo__24eo_5fprog_5fnot_5fand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_and x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_equiv_elim1`. -/
def eo__24eo_5fprog_5fnot_5fequiv_5felim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_equiv_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_equiv_elim2`. -/
def eo__24eo_5fprog_5fnot_5fequiv_5felim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_equiv_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_implies_elim1`. -/
def eo__24eo_5fprog_5fnot_5fimplies_5felim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fimplies_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_implies_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_implies_elim2`. -/
def eo__24eo_5fprog_5fnot_5fimplies_5felim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fimplies_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_implies_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_ite_elim1`. -/
def eo__24eo_5fprog_5fnot_5fite_5felim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_ite_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_ite_elim2`. -/
def eo__24eo_5fprog_5fnot_5fite_5felim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_ite_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_not_elim`. -/
def eo__24eo_5fprog_5fnot_5fnot_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fnot_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_not_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_xor_elim1`. -/
def eo__24eo_5fprog_5fnot_5fxor_5felim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_xor_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_not_xor_elim2`. -/
def eo__24eo_5fprog_5fnot_5fxor_5felim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fnot_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_xor_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-diff-elim`. -/
def eo__24eo_5fprog_5fre_2ddiff_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2ddiff_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_diff_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-in-comp`. -/
def eo__24eo_5fprog_5fre_2din_2dcomp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2din_2dcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_comp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-in-cstring`. -/
def eo__24eo_5fprog_5fre_2din_2dcstring.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2din_2dcstring s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_cstring x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-in-empty`. -/
def eo__24eo_5fprog_5fre_2din_2dempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_2din_2dempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-in-sigma-star`. -/
def eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_sigma_star x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-loop-neg`. -/
def eo__24eo_5fprog_5fre_2dloop_2dneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fre_2dloop_2dneg s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_loop_neg x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-repeat-elim`. -/
def eo__24eo_5fprog_5fre_2drepeat_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2drepeat_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_repeat_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-star-star`. -/
def eo__24eo_5fprog_5fre_2dstar_2dstar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_2dstar_2dstar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_star_star x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-union-const-elim`. -/
def eo__24eo_5fprog_5fre_2dunion_2dconst_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fre_2dunion_2dconst_2delim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_union_const_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re_inter`. -/
def eo__24eo_5fprog_5fre_5finter.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_5finter s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_inter x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_refl`. -/
def eo__24eo_5fprog_5frefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5frefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_refl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_scope`. -/
def eo__24eo_5fprog_5fscope.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → ProofOK x_a1 →
    eo__24eo_5fprog_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_scope x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_seq-len-rev`. -/
def eo__24eo_5fprog_5fseq_2dlen_2drev.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fseq_2dlen_2drev s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_seq_len_rev x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_seq-rev-rev`. -/
def eo__24eo_5fprog_5fseq_2drev_2drev.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fseq_2drev_2drev s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_seq_rev_rev x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_seq-rev-unit`. -/
def eo__24eo_5fprog_5fseq_2drev_2dunit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fseq_2drev_2dunit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_seq_rev_unit x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-choose-singleton`. -/
def eo__24eo_5fprog_5fsets_2dchoose_2dsingleton.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsets_2dchoose_2dsingleton s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_choose_singleton x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-eq-singleton-emp`. -/
def eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_eq_singleton_emp x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-insert-elim`. -/
def eo__24eo_5fprog_5fsets_2dinsert_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fsets_2dinsert_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_insert_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-inter-comm`. -/
def eo__24eo_5fprog_5fsets_2dinter_2dcomm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fsets_2dinter_2dcomm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_inter_comm x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-inter-emp1`. -/
def eo__24eo_5fprog_5fsets_2dinter_2demp1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2dinter_2demp1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_inter_emp1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-inter-emp2`. -/
def eo__24eo_5fprog_5fsets_2dinter_2demp2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2dinter_2demp2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_inter_emp2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-inter-member`. -/
def eo__24eo_5fprog_5fsets_2dinter_2dmember.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fsets_2dinter_2dmember s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_inter_member x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-inter-self`. -/
def eo__24eo_5fprog_5fsets_2dinter_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsets_2dinter_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_inter_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-is-empty-elim`. -/
def eo__24eo_5fprog_5fsets_2dis_2dempty_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fsets_2dis_2dempty_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_is_empty_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-is-singleton-elim`. -/
def eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_is_singleton_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-member-emp`. -/
def eo__24eo_5fprog_5fsets_2dmember_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2dmember_2demp s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_member_emp x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-member-singleton`. -/
def eo__24eo_5fprog_5fsets_2dmember_2dsingleton.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fsets_2dmember_2dsingleton s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_member_singleton x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-minus-emp1`. -/
def eo__24eo_5fprog_5fsets_2dminus_2demp1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2dminus_2demp1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_minus_emp1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-minus-emp2`. -/
def eo__24eo_5fprog_5fsets_2dminus_2demp2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2dminus_2demp2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_minus_emp2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-minus-member`. -/
def eo__24eo_5fprog_5fsets_2dminus_2dmember.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fsets_2dminus_2dmember s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_minus_member x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-minus-self`. -/
def eo__24eo_5fprog_5fsets_2dminus_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fsets_2dminus_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_minus_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-subset-elim`. -/
def eo__24eo_5fprog_5fsets_2dsubset_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fsets_2dsubset_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_subset_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-union-comm`. -/
def eo__24eo_5fprog_5fsets_2dunion_2dcomm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fsets_2dunion_2dcomm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_union_comm x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-union-emp1`. -/
def eo__24eo_5fprog_5fsets_2dunion_2demp1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2dunion_2demp1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_union_emp1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-union-emp2`. -/
def eo__24eo_5fprog_5fsets_2dunion_2demp2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fsets_2dunion_2demp2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_union_emp2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-union-member`. -/
def eo__24eo_5fprog_5fsets_2dunion_2dmember.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fsets_2dunion_2dmember s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_union_member x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets-union-self`. -/
def eo__24eo_5fprog_5fsets_2dunion_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsets_2dunion_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_union_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets_ext`. -/
def eo__24eo_5fprog_5fsets_5fext.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsets_5fext s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_ext x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_sets_singleton_inj`. -/
def eo__24eo_5fprog_5fsets_5fsingleton_5finj.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsets_5fsingleton_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_singleton_inj x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_skolem_intro`. -/
def eo__24eo_5fprog_5fskolem_5fintro.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fskolem_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_skolem_intro x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_split`. -/
def eo__24eo_5fprog_5fsplit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_split x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-leq-len-eq`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_leq_len_eq x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-refl`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2drefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dcontains_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_refl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-repl-self`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-repl-tgt`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_tgt x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-ctn-full-false1`. -/
def eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_ctn_full_false1 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-ctn-full-false2`. -/
def eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_ctn_full_false2 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-len-false`. -/
def eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_len_false x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-repl-no-change`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_no_change x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-repl-self-src`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_self_src x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-repl-tgt-eq-len`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_tgt_eq_len x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-len-replace-all-inv`. -/
def eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_len_replace_all_inv x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-len-replace-inv`. -/
def eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_len_replace_inv x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-len-update-inv`. -/
def eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_len_update_inv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-leq-concat-base-1`. -/
def eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d1 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_leq_concat_base_1 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-leq-concat-base-2`. -/
def eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_leq_concat_base_2 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-lt-elim`. -/
def eo__24eo_5fprog_5fstr_2dlt_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dlt_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_lt_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-prefixof-eq`. -/
def eo__24eo_5fprog_5fstr_2dprefixof_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dprefixof_2deq s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_prefixof_eq x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-dual-ite1`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_dual_ite1 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-dual-self`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_dual_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-len-id`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlen_2did.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlen_2did s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_len_id x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-src-inv-no-ctn1`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-src-inv-no-ctn2`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-src-self`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_self x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-src-tgt-no-ctn`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-tgt-no-ctn`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-tgt-self`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_tgt_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-all-id`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dall_2did.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dreplace_2dall_2did s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_id x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-all-no-contains`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_no_contains x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-dual-ctn`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_dual_ctn x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-dual-ctn-false`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_dual_ctn_false x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-id`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2did.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dreplace_2did s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_id x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-no-contains`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_no_contains x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-prefix`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dprefix.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dreplace_2dprefix s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_prefix x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-re-all-none`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_re_all_none x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-re-none`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_re_none x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-self`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dreplace_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-replace-self-ctn-simp`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_self_ctn_simp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-ctn`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dctn.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dctn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_ctn x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-ctn-contra`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dctn_2dcontra.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dctn_2dcontra s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_ctn_contra x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-len-norm`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_len_norm x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-suffixof-elim`. -/
def eo__24eo_5fprog_5fstr_2dsuffixof_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dsuffixof_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_suffixof_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-suffixof-eq`. -/
def eo__24eo_5fprog_5fstr_2dsuffixof_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dsuffixof_2deq s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_suffixof_eq x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-lower-from-int`. -/
def eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_from_int x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-lower-idem`. -/
def eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dlower_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_idem x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-lower-len`. -/
def eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_len x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-lower-upper`. -/
def eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_upper x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-upper-from-int`. -/
def eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_from_int x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-upper-idem`. -/
def eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dupper_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_idem x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-upper-len`. -/
def eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_len x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-upper-lower`. -/
def eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_lower x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_string_seq_unit_inj`. -/
def eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstring_5fseq_5funit_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_seq_unit_inj x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_symm`. -/
def eo__24eo_5fprog_5fsymm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_symm x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_trans`. -/
def eo__24eo_5fprog_5ftrans.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5ftrans s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_trans x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_true_elim`. -/
def eo__24eo_5fprog_5ftrue_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5ftrue_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_true_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_true_intro`. -/
def eo__24eo_5fprog_5ftrue_5fintro.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → ProofOK x_a0 →
    eo__24eo_5fprog_5ftrue_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_true_intro x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_trust`. -/
def eo__24eo_5fprog_5ftrust.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5ftrust s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_trust x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_uf-bv2nat-int2bv`. -/
def eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_uf-int2bv-bv2nat`. -/
def eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bv2nat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_uf-int2bv-bvule-equiv`. -/
def eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bvule_equiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_uf-int2bv-bvult-equiv`. -/
def eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bvult_equiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_xor_elim1`. -/
def eo__24eo_5fprog_5fxor_5felim1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_xor_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_xor_elim2`. -/
def eo__24eo_5fprog_5fxor_5felim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_xor_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_push_assume_check`. -/
def eo__24eo_5fpush_5fassume_5fcheck.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → StateOK x_a2 →
    eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_push_input_assume_check`. -/
def eo__24eo_5fpush_5finput_5fassume_5fcheck.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → StateOK x_a2 →
    eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_input_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_push_proven_check`. -/
def eo__24eo_5fpush_5fproven_5fcheck.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → StateOK x_a2 →
    eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_proven_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_state_is_closed`. -/
def eo__24eo_5fstate_5fis_5fclosed.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → StateOK x_a0 →
    eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_state_is_refutation`. -/
def eo__24eo_5fstate_5fis_5frefutation.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → StateOK x_a0 →
    eo__24eo_5fstate_5fis_5frefutation s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_refutation x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_state_proven_nth`. -/
def eo__24eo_5fstate_5fproven_5fnth.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
    eo__24eo_5fstate_5fproven_5fnth s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_proven_nth x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_array_deq_diff`. -/
def eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_array_deq_diff x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_nat`. -/
def eo__24eo_5fto_5fsmt_5fnat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fnat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_nat x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_nat_is_valid`. -/
def eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_nat_is_valid x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_re_unfold_pos_component`. -/
def eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_re_unfold_pos_component x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_reserved_datatype_name`. -/
def eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_reserved_datatype_name x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_seq.empty`. -/
def eo__24eo_5fto_5fsmt_5fseq_2eempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_seq_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_set.empty`. -/
def eo__24eo_5fto_5fsmt_5fset_2eempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_set_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_set_elem_type`. -/
def eo__24eo_5fto_5fsmt_5fset_5felem_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_set_elem_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_sets_deq_diff`. -/
def eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_sets_deq_diff x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_tester`. -/
def eo__24eo_5fto_5fsmt_5ftester.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5ftester s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tester x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_tuple_decl`. -/
def eo__24eo_5fto_5fsmt_5ftuple_5fdecl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5ftuple_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tuple_decl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_tuple_prepend_rec`. -/
def eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tuple_prepend_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_=`. -/
def eo__24eo_5ftypeof_5f_3d.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@@Pair`. -/
def eo__24eo_5ftypeof_5f_40_40Pair.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40_40Pair s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_Pair x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@@TypedList.cons`. -/
def eo__24eo_5ftypeof_5f_40_40TypedList_2econs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40_40TypedList_2econs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_TypedList_cons x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@@TypedList.nil`. -/
def eo__24eo_5ftypeof_5f_40_40TypedList_2enil.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40_40TypedList_2enil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_TypedList_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@@aci_sorted`. -/
def eo__24eo_5ftypeof_5f_40_40aci_5fsorted.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40_40aci_5fsorted s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_aci_sorted x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@@mon`. -/
def eo__24eo_5ftypeof_5f_40_40mon.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40_40mon s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_mon x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@@pair`. -/
def eo__24eo_5ftypeof_5f_40_40pair.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40_40pair s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_pair x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@@poly`. -/
def eo__24eo_5ftypeof_5f_40_40poly.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40_40poly s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_poly x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@array_deq_diff`. -/
def eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_array_deq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@bit`. -/
def eo__24eo_5ftypeof_5f_40bit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40bit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_bit x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@bvsize`. -/
def eo__24eo_5ftypeof_5f_40bvsize.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5f_40bvsize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_bvsize x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@const`. -/
def eo__24eo_5ftypeof_5f_40const.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5f_40const s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_const x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@div_by_zero`. -/
def eo__24eo_5ftypeof_5f_40div_5fby_5fzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5f_40div_5fby_5fzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_div_by_zero x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@purify`. -/
def eo__24eo_5ftypeof_5f_40purify.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5f_40purify s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_purify x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@re_unfold_pos_component`. -/
def eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_re_unfold_pos_component x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@sets_deq_diff`. -/
def eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_sets_deq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@strings_deq_diff`. -/
def eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_deq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@strings_num_occur_re`. -/
def eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_num_occur_re x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@strings_replace_all_result`. -/
def eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_replace_all_result x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@strings_replace_re_all_result`. -/
def eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_replace_re_all_result x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@strings_stoi_result`. -/
def eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_stoi_result x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@witness_string_length`. -/
def eo__24eo_5ftypeof_5f_40witness_5fstring_5flength.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5ftypeof_5f_40witness_5fstring_5flength s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_witness_string_length x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_BitVec`. -/
def eo__24eo_5ftypeof_5fBitVec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fBitVec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_BitVec x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_Seq`. -/
def eo__24eo_5ftypeof_5fSeq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fSeq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_Seq x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_apply`. -/
def eo__24eo_5ftypeof_5fapply.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_apply x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_bvand`. -/
def eo__24eo_5ftypeof_5fbvand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fbvand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvand x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_bvnego`. -/
def eo__24eo_5ftypeof_5fbvnego.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fbvnego s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvnego x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_bvnot`. -/
def eo__24eo_5ftypeof_5fbvnot.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fbvnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvnot x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_bvult`. -/
def eo__24eo_5ftypeof_5fbvult.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fbvult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvult x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_distinct`. -/
def eo__24eo_5ftypeof_5fdistinct.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fdistinct s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_distinct x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_div`. -/
def eo__24eo_5ftypeof_5fdiv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fdiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_div x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_divisible`. -/
def eo__24eo_5ftypeof_5fdivisible.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fdivisible s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_divisible x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_dt_cons_rec`. -/
def eo__24eo_5ftypeof_5fdt_5fcons_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_dt_sel_return`. -/
def eo__24eo_5ftypeof_5fdt_5fsel_5freturn.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fdt_5fsel_5freturn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_dt_sel_return x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_forall`. -/
def eo__24eo_5ftypeof_5fforall.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fforall s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_forall x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_fun_type`. -/
def eo__24eo_5ftypeof_5ffun_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5ffun_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_fun_type x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_int.ispow2`. -/
def eo__24eo_5ftypeof_5fint_2eispow2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fint_2eispow2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_int_ispow2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_int.pow2`. -/
def eo__24eo_5ftypeof_5fint_2epow2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fint_2epow2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_int_pow2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_is`. -/
def eo__24eo_5ftypeof_5fis.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fis s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_is x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_is_int`. -/
def eo__24eo_5ftypeof_5fis_5fint.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fis_5fint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_is_int x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_ite`. -/
def eo__24eo_5ftypeof_5fite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_lambda`. -/
def eo__24eo_5ftypeof_5flambda.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5flambda s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_lambda x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_not`. -/
def eo__24eo_5ftypeof_5fnot.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_not x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_or`. -/
def eo__24eo_5ftypeof_5for.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5for s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_or x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_re.*`. -/
def eo__24eo_5ftypeof_5fre_2e_2a.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fre_2e_2a s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_re_mult x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_re.++`. -/
def eo__24eo_5ftypeof_5fre_2e_2b_2b.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fre_2e_2b_2b s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_re_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_re.range`. -/
def eo__24eo_5ftypeof_5fre_2erange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fre_2erange s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_re_range x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_select`. -/
def eo__24eo_5ftypeof_5fselect.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fselect s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_select x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_seq.empty`. -/
def eo__24eo_5ftypeof_5fseq_2eempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fseq_2eempty s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_seq_empty x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_seq.nth`. -/
def eo__24eo_5ftypeof_5fseq_2enth.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fseq_2enth s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_seq_nth x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_seq.unit`. -/
def eo__24eo_5ftypeof_5fseq_2eunit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fseq_2eunit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_seq_unit x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.choose`. -/
def eo__24eo_5ftypeof_5fset_2echoose.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fset_2echoose s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_choose x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.empty`. -/
def eo__24eo_5ftypeof_5fset_2eempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fset_2eempty s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_empty x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.insert`. -/
def eo__24eo_5ftypeof_5fset_2einsert.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fset_2einsert s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_insert x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.is_empty`. -/
def eo__24eo_5ftypeof_5fset_2eis_5fempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fset_2eis_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_is_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.member`. -/
def eo__24eo_5ftypeof_5fset_2emember.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fset_2emember s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_member x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.singleton`. -/
def eo__24eo_5ftypeof_5fset_2esingleton.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fset_2esingleton s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_singleton x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.subset`. -/
def eo__24eo_5ftypeof_5fset_2esubset.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fset_2esubset s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_subset x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_set.union`. -/
def eo__24eo_5ftypeof_5fset_2eunion.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fset_2eunion s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_set_union x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_store`. -/
def eo__24eo_5ftypeof_5fstore.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fstore s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_store x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.++`. -/
def eo__24eo_5ftypeof_5fstr_2e_2b_2b.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fstr_2e_2b_2b s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.<`. -/
def eo__24eo_5ftypeof_5fstr_2e_3c.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fstr_2e_3c s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_lt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.at`. -/
def eo__24eo_5ftypeof_5fstr_2eat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fstr_2eat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_at x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.contains`. -/
def eo__24eo_5ftypeof_5fstr_2econtains.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fstr_2econtains s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_contains x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.from_code`. -/
def eo__24eo_5ftypeof_5fstr_2efrom_5fcode.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fstr_2efrom_5fcode s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_from_code x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.in_re`. -/
def eo__24eo_5ftypeof_5fstr_2ein_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fstr_2ein_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_in_re x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.indexof`. -/
def eo__24eo_5ftypeof_5fstr_2eindexof.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fstr_2eindexof s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_indexof x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.indexof_re`. -/
def eo__24eo_5ftypeof_5fstr_2eindexof_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fstr_2eindexof_5fre s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_indexof_re x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.is_digit`. -/
def eo__24eo_5ftypeof_5fstr_2eis_5fdigit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fstr_2eis_5fdigit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_is_digit x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.len`. -/
def eo__24eo_5ftypeof_5fstr_2elen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fstr_2elen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_len x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.replace`. -/
def eo__24eo_5ftypeof_5fstr_2ereplace.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fstr_2ereplace s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_replace x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.replace_re`. -/
def eo__24eo_5ftypeof_5fstr_2ereplace_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fstr_2ereplace_5fre s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_replace_re x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.rev`. -/
def eo__24eo_5ftypeof_5fstr_2erev.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fstr_2erev s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_rev x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.substr`. -/
def eo__24eo_5ftypeof_5fstr_2esubstr.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fstr_2esubstr s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_substr x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.to_code`. -/
def eo__24eo_5ftypeof_5fstr_2eto_5fcode.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fstr_2eto_5fcode s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_to_code x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.to_lower`. -/
def eo__24eo_5ftypeof_5fstr_2eto_5flower.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fstr_2eto_5flower s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_to_lower x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.to_re`. -/
def eo__24eo_5ftypeof_5fstr_2eto_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fstr_2eto_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_to_re x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_str.update`. -/
def eo__24eo_5ftypeof_5fstr_2eupdate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fstr_2eupdate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_str_update x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_to_int`. -/
def eo__24eo_5ftypeof_5fto_5fint.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fto_5fint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_to_int x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_to_real`. -/
def eo__24eo_5ftypeof_5fto_5freal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fto_5freal s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_to_real x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_update`. -/
def eo__24eo_5ftypeof_5fupdate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fupdate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_update x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$from_clause`. -/
def eo__24from_5fclause.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24from_5fclause s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__from_clause x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$get_arg_list_rec`. -/
def eo__24get_5farg_5flist_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24get_5farg_5flist_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__get_arg_list_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$get_lambda_type`. -/
def eo__24get_5flambda_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24get_5flambda_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__get_lambda_type x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$get_var_type`. -/
def eo__24get_5fvar_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24get_5fvar_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__get_var_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$is_arith_type`. -/
def eo__24is_5farith_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24is_5farith_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_arith_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$is_seq_const`. -/
def eo__24is_5fseq_5fconst.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24is_5fseq_5fconst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_seq_const x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$is_seq_const_rec`. -/
def eo__24is_5fseq_5fconst_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24is_5fseq_5fconst_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_seq_const_rec x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$lower_not_and`. -/
def eo__24lower_5fnot_5fand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24lower_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__lower_not_and x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_arith_sum_ub_rec`. -/
def eo__24mk_5farith_5fsum_5fub_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5farith_5fsum_5fub_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_sum_ub_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_arith_trichotomy`. -/
def eo__24mk_5farith_5ftrichotomy.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5farith_5ftrichotomy s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_trichotomy x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_distinct_elim`. -/
def eo__24mk_5fdistinct_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24mk_5fdistinct_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_distinct_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_distinct_elim_rec`. -/
def eo__24mk_5fdistinct_5felim_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fdistinct_5felim_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_distinct_elim_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_dt_inst_rec`. -/
def eo__24mk_5fdt_5finst_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fdt_5finst_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_dt_split`. -/
def eo__24mk_5fdt_5fsplit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5fdt_5fsplit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_split x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_ho_cong`. -/
def eo__24mk_5fho_5fcong.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fho_5fcong s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_ho_cong x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_quant_miniscope_and`. -/
def eo__24mk_5fquant_5fminiscope_5fand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5fquant_5fminiscope_5fand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_quant_miniscope_and x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_re_concat`. -/
def eo__24mk_5fre_5fconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5fre_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_symm`. -/
def eo__24mk_5fsymm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24mk_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_symm x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_trans`. -/
def eo__24mk_5ftrans.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_trans x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$pair_first`. -/
def eo__24pair_5ffirst.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24pair_5ffirst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__pair_first x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$pair_second`. -/
def eo__24pair_5fsecond.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24pair_5fsecond s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__pair_second x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_split_str_to_re`. -/
def eo__24re_5fsplit_5fstr_5fto_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24re_5fsplit_5fstr_5fto_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_split_str_to_re x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$seq_element_of_unit`. -/
def eo__24seq_5felement_5fof_5funit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24seq_5felement_5fof_5funit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__seq_element_of_unit x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$seq_is_non_empty`. -/
def eo__24seq_5fis_5fnon_5fempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24seq_5fis_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__seq_is_non_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dd_has_dt`. -/
def eo__24smtx_5fdd_5fhas_5fdt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdd_5fhas_5fdt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dd_has_dt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dd_lookup`. -/
def eo__24smtx_5fdd_5flookup.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dd_lookup x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_decl_inhabited`. -/
def eo__24smtx_5fdecl_5finhabited.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdecl_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_decl_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_decl_wf_rec`. -/
def eo__24smtx_5fdecl_5fwf_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdecl_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_decl_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dt_cons_inhabited`. -/
def eo__24smtx_5fdt_5fcons_5finhabited.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_cons_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dt_cons_wf_rec`. -/
def eo__24smtx_5fdt_5fcons_5fwf_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_cons_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dt_inhabited`. -/
def eo__24smtx_5fdt_5finhabited.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdt_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dt_resolve`. -/
def eo__24smtx_5fdt_5fresolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dt_wf_rec`. -/
def eo__24smtx_5fdt_5fwf_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdt_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dtc_num_sels`. -/
def eo__24smtx_5fdtc_5fnum_5fsels.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5fdtc_5fnum_5fsels s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dtc_num_sels x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_dtc_resolve`. -/
def eo__24smtx_5fdtc_5fresolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dtc_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_inhabited_type`. -/
def eo__24smtx_5finhabited_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_inhabited_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_ret_typeof_sel`. -/
def eo__24smtx_5fret_5ftypeof_5fsel.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24smtx_5fret_5ftypeof_5fsel s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_ret_typeof_sel_rec`. -/
def eo__24smtx_5fret_5ftypeof_5fsel_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_type_wf`. -/
def eo__24smtx_5ftype_5fwf.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_type_wf_component`. -/
def eo__24smtx_5ftype_5fwf_5fcomponent.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5ftype_5fwf_5fcomponent s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf_component x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_type_wf_rec`. -/
def eo__24smtx_5ftype_5fwf_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf_rec x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_=`. -/
def eo__24smtx_5ftypeof_5f_3d.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_apply`. -/
def eo__24smtx_5ftypeof_5fapply.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_apply x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_arith_overload_op_1`. -/
def eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_arith_overload_op_1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_arith_overload_op_2`. -/
def eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_arith_overload_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_arith_overload_op_2_ret`. -/
def eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_arith_overload_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_bv_op_1`. -/
def eo__24smtx_5ftypeof_5fbv_5fop_5f1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5ftypeof_5fbv_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_bv_op_1_ret`. -/
def eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_1_ret x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_dt_cons_rec`. -/
def eo__24smtx_5ftypeof_5fdt_5fcons_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_guard`. -/
def eo__24smtx_5ftypeof_5fguard.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fguard s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_guard x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_guard_wf`. -/
def eo__24smtx_5ftypeof_5fguard_5fwf.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fguard_5fwf s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_guard_wf x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_int_to_bv`. -/
def eo__24smtx_5ftypeof_5fint_5fto_5fbv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fint_5fto_5fbv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_int_to_bv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_ite`. -/
def eo__24smtx_5ftypeof_5fite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_map_diff`. -/
def eo__24smtx_5ftypeof_5fmap_5fdiff.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fmap_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_map_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_re.^`. -/
def eo__24smtx_5ftypeof_5fre_2e_5e.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fre_2e_5e s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_re_exp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_re.loop`. -/
def eo__24smtx_5ftypeof_5fre_2eloop.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fre_2eloop s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_re_loop x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_rotate_left`. -/
def eo__24smtx_5ftypeof_5frotate_5fleft.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5frotate_5fleft s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_rotate_left x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_rotate_right`. -/
def eo__24smtx_5ftypeof_5frotate_5fright.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5frotate_5fright s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_rotate_right x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_select`. -/
def eo__24smtx_5ftypeof_5fselect.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fselect s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_select x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_seq.nth`. -/
def eo__24smtx_5ftypeof_5fseq_2enth.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fseq_2enth s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_nth x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_seq_diff`. -/
def eo__24smtx_5ftypeof_5fseq_5fdiff.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fseq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_seq_op_1`. -/
def eo__24smtx_5ftypeof_5fseq_5fop_5f1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5ftypeof_5fseq_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_seq_op_1_ret`. -/
def eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_1_ret x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_seq_op_2`. -/
def eo__24smtx_5ftypeof_5fseq_5fop_5f2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fseq_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_seq_op_2_ret`. -/
def eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_seq_op_3`. -/
def eo__24smtx_5ftypeof_5fseq_5fop_5f3.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fseq_5fop_5f3 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_3 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_set.member`. -/
def eo__24smtx_5ftypeof_5fset_2emember.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fset_2emember s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_set_member x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_sets_op_2`. -/
def eo__24smtx_5ftypeof_5fsets_5fop_5f2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fsets_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_sets_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_sets_op_2_ret`. -/
def eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_sets_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_store`. -/
def eo__24smtx_5ftypeof_5fstore.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fstore s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_store x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_str.at`. -/
def eo__24smtx_5ftypeof_5fstr_2eat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fstr_2eat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_at x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_str.indexof`. -/
def eo__24smtx_5ftypeof_5fstr_2eindexof.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fstr_2eindexof s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_indexof x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_str.substr`. -/
def eo__24smtx_5ftypeof_5fstr_2esubstr.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fstr_2esubstr s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_substr x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_str.update`. -/
def eo__24smtx_5ftypeof_5fstr_2eupdate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fstr_2eupdate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_update x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_membership_re`. -/
def eo__24str_5fmembership_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24str_5fmembership_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_membership_re x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_membership_str`. -/
def eo__24str_5fmembership_5fstr.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24str_5fmembership_5fstr s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_membership_str x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$to_clause`. -/
def eo__24to_5fclause.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24to_5fclause s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__to_clause x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$to_cube`. -/
def eo__24to_5fcube.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24to_5fcube s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__to_cube x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$tuple_arg_list`. -/
def eo__24tuple_5farg_5flist.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24tuple_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__tuple_arg_list x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$typed_list_element_type`. -/
def eo__24typed_5flist_5felement_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24typed_5flist_5felement_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__typed_list_element_type x_a0)
      | core.result.Result.Err _ => True ⦄div

@[simp] theorem Valid.uop1 (op : Eo.UserOp1) (i0 : Eo.Term) :
    Valid.valid (Eo.Term.UOp1 op i0) ↔ Valid.valid i0 := by
  show TreeValid (Embed.enc_Term _) ↔ _
  simp only [Embed.enc_Term, TreeValid, TreesValid, and_true]
  rfl

@[simp] theorem Valid.uop2 (op : Eo.UserOp2) (i0 : Eo.Term) (i1 : Eo.Term) :
    Valid.valid (Eo.Term.UOp2 op i0 i1) ↔ Valid.valid i0 ∧ Valid.valid i1 := by
  show TreeValid (Embed.enc_Term _) ↔ _
  simp only [Embed.enc_Term, TreeValid, TreesValid, and_true]
  rfl

@[simp] theorem Valid.uop3 (op : Eo.UserOp3) (i0 : Eo.Term) (i1 : Eo.Term) (i2 : Eo.Term) :
    Valid.valid (Eo.Term.UOp3 op i0 i1 i2) ↔ Valid.valid i0 ∧ Valid.valid i1 ∧ Valid.valid i2 := by
  show TreeValid (Embed.enc_Term _) ↔ _
  simp only [Embed.enc_Term, TreeValid, TreesValid, and_true]
  rfl

/-- What is proved of the programs, for stores that can enter `n` more calls. -/
structure Specs (n : Nat) : Prop where
  eo__24arith_5fnormalize_5flit : eo__24arith_5fnormalize_5flit.Spec n
  eo__24arith_5frel_5finv : eo__24arith_5frel_5finv.Spec n
  eo__24arith_5frel_5fneg : eo__24arith_5frel_5fneg.Spec n
  eo__24arith_5frel_5fsum : eo__24arith_5frel_5fsum.Spec n
  eo__24arith_5frel_5ftrichotomy : eo__24arith_5frel_5ftrichotomy.Spec n
  eo__24bv_5fbitblast_5fbinary_5fapp : eo__24bv_5fbitblast_5fbinary_5fapp.Spec n
  eo__24bv_5fbitblast_5fhead : eo__24bv_5fbitblast_5fhead.Spec n
  eo__24bv_5fbitblast_5ftail : eo__24bv_5fbitblast_5ftail.Spec n
  eo__24bv_5fbitwidth : eo__24bv_5fbitwidth.Spec n
  eo__24dt_5farg_5flist : eo__24dt_5farg_5flist.Spec n
  eo__24eo_5fStateObj_5fproven : eo__24eo_5fStateObj_5fproven.Spec n
  eo__24eo_5fcmd_5fstep_5fpop_5fproven : eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec n
  eo__24eo_5fdd_5flookup : eo__24eo_5fdd_5flookup.Spec n
  eo__24eo_5fdd_5fresolve : eo__24eo_5fdd_5fresolve.Spec n
  eo__24eo_5fdisamb_5ftype_5fseq_2eempty : eo__24eo_5fdisamb_5ftype_5fseq_2eempty.Spec n
  eo__24eo_5fdisamb_5ftype_5fset_2eempty : eo__24eo_5fdisamb_5ftype_5fset_2eempty.Spec n
  eo__24eo_5fdt_5fresolve : eo__24eo_5fdt_5fresolve.Spec n
  eo__24eo_5fdtc_5fresolve : eo__24eo_5fdtc_5fresolve.Spec n
  eo__24eo_5finvoke_5fcmd_5fcheck_5fproven : eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec n
  eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs : eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.Spec n
  eo__24eo_5flit_5ftype_5fBinary : eo__24eo_5flit_5ftype_5fBinary.Spec n
  eo__24eo_5flit_5ftype_5fNumeral : eo__24eo_5flit_5ftype_5fNumeral.Spec n
  eo__24eo_5flit_5ftype_5fRational : eo__24eo_5flit_5ftype_5fRational.Spec n
  eo__24eo_5flit_5ftype_5fString : eo__24eo_5flit_5ftype_5fString.Spec n
  eo__24eo_5fnil_5f_40_40TypedList_2econs : eo__24eo_5fnil_5f_40_40TypedList_2econs.Spec n
  eo__24eo_5fprog_5fand_5fintro : eo__24eo_5fprog_5fand_5fintro.Spec n
  eo__24eo_5fprog_5farith_2dabs_2deq : eo__24eo_5fprog_5farith_2dabs_2deq.Spec n
  eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal : eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal.Spec n
  eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal : eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal.Spec n
  eo__24eo_5fprog_5farith_2delim_2dgt : eo__24eo_5fprog_5farith_2delim_2dgt.Spec n
  eo__24eo_5fprog_5farith_2delim_2dleq : eo__24eo_5fprog_5farith_2delim_2dleq.Spec n
  eo__24eo_5fprog_5farith_2delim_2dlt : eo__24eo_5fprog_5farith_2delim_2dlt.Spec n
  eo__24eo_5fprog_5farith_2deq_2delim_2dint : eo__24eo_5fprog_5farith_2deq_2delim_2dint.Spec n
  eo__24eo_5fprog_5farith_2deq_2delim_2dreal : eo__24eo_5fprog_5farith_2deq_2delim_2dreal.Spec n
  eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift : eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift.Spec n
  eo__24eo_5fprog_5farith_2dint_2deq_2dconflict : eo__24eo_5fprog_5farith_2dint_2deq_2dconflict.Spec n
  eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal : eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal.Spec n
  eo__24eo_5fprog_5farith_2dleq_2dite_2dlift : eo__24eo_5fprog_5farith_2dleq_2dite_2dlift.Spec n
  eo__24eo_5fprog_5farith_2dmax_2dgeq1 : eo__24eo_5fprog_5farith_2dmax_2dgeq1.Spec n
  eo__24eo_5fprog_5farith_2dmax_2dgeq2 : eo__24eo_5fprog_5farith_2dmax_2dgeq2.Spec n
  eo__24eo_5fprog_5farith_2dmin_2dlt1 : eo__24eo_5fprog_5farith_2dmin_2dlt1.Spec n
  eo__24eo_5fprog_5farith_2dmin_2dlt2 : eo__24eo_5fprog_5farith_2dmin_2dlt2.Spec n
  eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal : eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal.Spec n
  eo__24eo_5fprog_5farith_5ftrichotomy : eo__24eo_5fprog_5farith_5ftrichotomy.Spec n
  eo__24eo_5fprog_5farray_2dread_2dover_2dwrite : eo__24eo_5fprog_5farray_2dread_2dover_2dwrite.Spec n
  eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit : eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit.Spec n
  eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2 : eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2.Spec n
  eo__24eo_5fprog_5farray_2dstore_2doverwrite : eo__24eo_5fprog_5farray_2dstore_2doverwrite.Spec n
  eo__24eo_5fprog_5farray_2dstore_2dself : eo__24eo_5fprog_5farray_2dstore_2dself.Spec n
  eo__24eo_5fprog_5farray_2dstore_2dswap : eo__24eo_5fprog_5farray_2dstore_2dswap.Spec n
  eo__24eo_5fprog_5farrays_5fext : eo__24eo_5fprog_5farrays_5fext.Spec n
  eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite : eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite.Spec n
  eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1 : eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1.Spec n
  eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim : eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim.Spec n
  eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq : eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq.Spec n
  eo__24eo_5fprog_5fbool_2deq_2dfalse : eo__24eo_5fprog_5fbool_2deq_2dfalse.Spec n
  eo__24eo_5fprog_5fbool_2deq_2dnrefl : eo__24eo_5fprog_5fbool_2deq_2dnrefl.Spec n
  eo__24eo_5fprog_5fbool_2deq_2dtrue : eo__24eo_5fprog_5fbool_2deq_2dtrue.Spec n
  eo__24eo_5fprog_5fbool_2dimpl_2delim : eo__24eo_5fprog_5fbool_2dimpl_2delim.Spec n
  eo__24eo_5fprog_5fbool_2dimpl_2dfalse1 : eo__24eo_5fprog_5fbool_2dimpl_2dfalse1.Spec n
  eo__24eo_5fprog_5fbool_2dimpl_2dfalse2 : eo__24eo_5fprog_5fbool_2dimpl_2dfalse2.Spec n
  eo__24eo_5fprog_5fbool_2dimpl_2dtrue1 : eo__24eo_5fprog_5fbool_2dimpl_2dtrue1.Spec n
  eo__24eo_5fprog_5fbool_2dimpl_2dtrue2 : eo__24eo_5fprog_5fbool_2dimpl_2dtrue2.Spec n
  eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan : eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1 : eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2 : eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dfalse : eo__24eo_5fprog_5fbool_2dnot_2dfalse.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dite_2delim : eo__24eo_5fprog_5fbool_2dnot_2dite_2delim.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dtrue : eo__24eo_5fprog_5fbool_2dnot_2dtrue.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim : eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dcomm : eo__24eo_5fprog_5fbool_2dxor_2dcomm.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2delim : eo__24eo_5fprog_5fbool_2dxor_2delim.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dfalse : eo__24eo_5fprog_5fbool_2dxor_2dfalse.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dnrefl : eo__24eo_5fprog_5fbool_2dxor_2dnrefl.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2drefl : eo__24eo_5fprog_5fbool_2dxor_2drefl.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dtrue : eo__24eo_5fprog_5fbool_2dxor_2dtrue.Spec n
  eo__24eo_5fprog_5fbv_2dcommutative_2dcomp : eo__24eo_5fprog_5fbv_2dcommutative_2dcomp.Spec n
  eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve : eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dnot : eo__24eo_5fprog_5fbv_2dextract_2dnot.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1 : eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren : eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2 : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3 : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3.Spec n
  eo__24eo_5fprog_5fbv_2dlt_2dself : eo__24eo_5fprog_5fbv_2dlt_2dself.Spec n
  eo__24eo_5fprog_5fbv_2dnot_2didemp : eo__24eo_5fprog_5fbv_2dnot_2didemp.Spec n
  eo__24eo_5fprog_5fbv_2dnot_2dult : eo__24eo_5fprog_5fbv_2dnot_2dult.Spec n
  eo__24eo_5fprog_5fbv_2dnot_2dxor : eo__24eo_5fprog_5fbv_2dnot_2dxor.Spec n
  eo__24eo_5fprog_5fbv_2dsge_2deliminate : eo__24eo_5fprog_5fbv_2dsge_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dsgt_2deliminate : eo__24eo_5fprog_5fbv_2dsgt_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dsle_2deliminate : eo__24eo_5fprog_5fbv_2dsle_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dsle_2dself : eo__24eo_5fprog_5fbv_2dsle_2dself.Spec n
  eo__24eo_5fprog_5fbv_2duge_2deliminate : eo__24eo_5fprog_5fbv_2duge_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dugt_2deliminate : eo__24eo_5fprog_5fbv_2dugt_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dule_2deliminate : eo__24eo_5fprog_5fbv_2dule_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dule_2dself : eo__24eo_5fprog_5fbv_2dule_2dself.Spec n
  eo__24eo_5fprog_5fbv_2dult_2dself : eo__24eo_5fprog_5fbv_2dult_2dself.Spec n
  eo__24eo_5fprog_5fcnf_5fand_5fneg : eo__24eo_5fprog_5fcnf_5fand_5fneg.Spec n
  eo__24eo_5fprog_5fcnf_5fequiv_5fneg1 : eo__24eo_5fprog_5fcnf_5fequiv_5fneg1.Spec n
  eo__24eo_5fprog_5fcnf_5fequiv_5fneg2 : eo__24eo_5fprog_5fcnf_5fequiv_5fneg2.Spec n
  eo__24eo_5fprog_5fcnf_5fequiv_5fpos1 : eo__24eo_5fprog_5fcnf_5fequiv_5fpos1.Spec n
  eo__24eo_5fprog_5fcnf_5fequiv_5fpos2 : eo__24eo_5fprog_5fcnf_5fequiv_5fpos2.Spec n
  eo__24eo_5fprog_5fcnf_5fimplies_5fneg1 : eo__24eo_5fprog_5fcnf_5fimplies_5fneg1.Spec n
  eo__24eo_5fprog_5fcnf_5fimplies_5fneg2 : eo__24eo_5fprog_5fcnf_5fimplies_5fneg2.Spec n
  eo__24eo_5fprog_5fcnf_5fimplies_5fpos : eo__24eo_5fprog_5fcnf_5fimplies_5fpos.Spec n
  eo__24eo_5fprog_5fcnf_5fite_5fneg1 : eo__24eo_5fprog_5fcnf_5fite_5fneg1.Spec n
  eo__24eo_5fprog_5fcnf_5fite_5fneg2 : eo__24eo_5fprog_5fcnf_5fite_5fneg2.Spec n
  eo__24eo_5fprog_5fcnf_5fite_5fneg3 : eo__24eo_5fprog_5fcnf_5fite_5fneg3.Spec n
  eo__24eo_5fprog_5fcnf_5fite_5fpos1 : eo__24eo_5fprog_5fcnf_5fite_5fpos1.Spec n
  eo__24eo_5fprog_5fcnf_5fite_5fpos2 : eo__24eo_5fprog_5fcnf_5fite_5fpos2.Spec n
  eo__24eo_5fprog_5fcnf_5fite_5fpos3 : eo__24eo_5fprog_5fcnf_5fite_5fpos3.Spec n
  eo__24eo_5fprog_5fcnf_5for_5fpos : eo__24eo_5fprog_5fcnf_5for_5fpos.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fneg1 : eo__24eo_5fprog_5fcnf_5fxor_5fneg1.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fneg2 : eo__24eo_5fprog_5fcnf_5fxor_5fneg2.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fpos1 : eo__24eo_5fprog_5fcnf_5fxor_5fpos1.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fpos2 : eo__24eo_5fprog_5fcnf_5fxor_5fpos2.Spec n
  eo__24eo_5fprog_5fcontra : eo__24eo_5fprog_5fcontra.Spec n
  eo__24eo_5fprog_5feq_2dcond_2ddeq : eo__24eo_5fprog_5feq_2dcond_2ddeq.Spec n
  eo__24eo_5fprog_5feq_2dite_2dlift : eo__24eo_5fprog_5feq_2dite_2dlift.Spec n
  eo__24eo_5fprog_5feq_2drefl : eo__24eo_5fprog_5feq_2drefl.Spec n
  eo__24eo_5fprog_5feq_2dsymm : eo__24eo_5fprog_5feq_2dsymm.Spec n
  eo__24eo_5fprog_5feq_5fresolve : eo__24eo_5fprog_5feq_5fresolve.Spec n
  eo__24eo_5fprog_5fequiv_5felim1 : eo__24eo_5fprog_5fequiv_5felim1.Spec n
  eo__24eo_5fprog_5fequiv_5felim2 : eo__24eo_5fprog_5fequiv_5felim2.Spec n
  eo__24eo_5fprog_5fexists_2delim : eo__24eo_5fprog_5fexists_2delim.Spec n
  eo__24eo_5fprog_5ffalse_5felim : eo__24eo_5fprog_5ffalse_5felim.Spec n
  eo__24eo_5fprog_5ffalse_5fintro : eo__24eo_5fprog_5ffalse_5fintro.Spec n
  eo__24eo_5fprog_5fho_5fcong : eo__24eo_5fprog_5fho_5fcong.Spec n
  eo__24eo_5fprog_5fimplies_5felim : eo__24eo_5fprog_5fimplies_5felim.Spec n
  eo__24eo_5fprog_5fite_2delse_2dfalse : eo__24eo_5fprog_5fite_2delse_2dfalse.Spec n
  eo__24eo_5fprog_5fite_2delse_2dlookahead : eo__24eo_5fprog_5fite_2delse_2dlookahead.Spec n
  eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself : eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself.Spec n
  eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself : eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself.Spec n
  eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead : eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead.Spec n
  eo__24eo_5fprog_5fite_2delse_2dtrue : eo__24eo_5fprog_5fite_2delse_2dtrue.Spec n
  eo__24eo_5fprog_5fite_2deq_2dbranch : eo__24eo_5fprog_5fite_2deq_2dbranch.Spec n
  eo__24eo_5fprog_5fite_2dexpand : eo__24eo_5fprog_5fite_2dexpand.Spec n
  eo__24eo_5fprog_5fite_2dfalse_2dcond : eo__24eo_5fprog_5fite_2dfalse_2dcond.Spec n
  eo__24eo_5fprog_5fite_2dneg_2dbranch : eo__24eo_5fprog_5fite_2dneg_2dbranch.Spec n
  eo__24eo_5fprog_5fite_2dnot_2dcond : eo__24eo_5fprog_5fite_2dnot_2dcond.Spec n
  eo__24eo_5fprog_5fite_2dthen_2dfalse : eo__24eo_5fprog_5fite_2dthen_2dfalse.Spec n
  eo__24eo_5fprog_5fite_2dthen_2dlookahead : eo__24eo_5fprog_5fite_2dthen_2dlookahead.Spec n
  eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself : eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.Spec n
  eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself : eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.Spec n
  eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead : eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.Spec n
  eo__24eo_5fprog_5fite_2dthen_2dtrue : eo__24eo_5fprog_5fite_2dthen_2dtrue.Spec n
  eo__24eo_5fprog_5fite_2dtrue_2dcond : eo__24eo_5fprog_5fite_2dtrue_2dcond.Spec n
  eo__24eo_5fprog_5fite_5felim1 : eo__24eo_5fprog_5fite_5felim1.Spec n
  eo__24eo_5fprog_5fite_5felim2 : eo__24eo_5fprog_5fite_5felim2.Spec n
  eo__24eo_5fprog_5fite_5feq : eo__24eo_5fprog_5fite_5feq.Spec n
  eo__24eo_5fprog_5fmodus_5fponens : eo__24eo_5fprog_5fmodus_5fponens.Spec n
  eo__24eo_5fprog_5fnot_5fand : eo__24eo_5fprog_5fnot_5fand.Spec n
  eo__24eo_5fprog_5fnot_5fequiv_5felim1 : eo__24eo_5fprog_5fnot_5fequiv_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fequiv_5felim2 : eo__24eo_5fprog_5fnot_5fequiv_5felim2.Spec n
  eo__24eo_5fprog_5fnot_5fimplies_5felim1 : eo__24eo_5fprog_5fnot_5fimplies_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fimplies_5felim2 : eo__24eo_5fprog_5fnot_5fimplies_5felim2.Spec n
  eo__24eo_5fprog_5fnot_5fite_5felim1 : eo__24eo_5fprog_5fnot_5fite_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fite_5felim2 : eo__24eo_5fprog_5fnot_5fite_5felim2.Spec n
  eo__24eo_5fprog_5fnot_5fnot_5felim : eo__24eo_5fprog_5fnot_5fnot_5felim.Spec n
  eo__24eo_5fprog_5fnot_5fxor_5felim1 : eo__24eo_5fprog_5fnot_5fxor_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fxor_5felim2 : eo__24eo_5fprog_5fnot_5fxor_5felim2.Spec n
  eo__24eo_5fprog_5fre_2ddiff_2delim : eo__24eo_5fprog_5fre_2ddiff_2delim.Spec n
  eo__24eo_5fprog_5fre_2din_2dcomp : eo__24eo_5fprog_5fre_2din_2dcomp.Spec n
  eo__24eo_5fprog_5fre_2din_2dcstring : eo__24eo_5fprog_5fre_2din_2dcstring.Spec n
  eo__24eo_5fprog_5fre_2din_2dempty : eo__24eo_5fprog_5fre_2din_2dempty.Spec n
  eo__24eo_5fprog_5fre_2din_2dsigma_2dstar : eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.Spec n
  eo__24eo_5fprog_5fre_2dloop_2dneg : eo__24eo_5fprog_5fre_2dloop_2dneg.Spec n
  eo__24eo_5fprog_5fre_2drepeat_2delim : eo__24eo_5fprog_5fre_2drepeat_2delim.Spec n
  eo__24eo_5fprog_5fre_2dstar_2dstar : eo__24eo_5fprog_5fre_2dstar_2dstar.Spec n
  eo__24eo_5fprog_5fre_2dunion_2dconst_2delim : eo__24eo_5fprog_5fre_2dunion_2dconst_2delim.Spec n
  eo__24eo_5fprog_5fre_5finter : eo__24eo_5fprog_5fre_5finter.Spec n
  eo__24eo_5fprog_5frefl : eo__24eo_5fprog_5frefl.Spec n
  eo__24eo_5fprog_5fscope : eo__24eo_5fprog_5fscope.Spec n
  eo__24eo_5fprog_5fseq_2dlen_2drev : eo__24eo_5fprog_5fseq_2dlen_2drev.Spec n
  eo__24eo_5fprog_5fseq_2drev_2drev : eo__24eo_5fprog_5fseq_2drev_2drev.Spec n
  eo__24eo_5fprog_5fseq_2drev_2dunit : eo__24eo_5fprog_5fseq_2drev_2dunit.Spec n
  eo__24eo_5fprog_5fsets_2dchoose_2dsingleton : eo__24eo_5fprog_5fsets_2dchoose_2dsingleton.Spec n
  eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp : eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp.Spec n
  eo__24eo_5fprog_5fsets_2dinsert_2delim : eo__24eo_5fprog_5fsets_2dinsert_2delim.Spec n
  eo__24eo_5fprog_5fsets_2dinter_2dcomm : eo__24eo_5fprog_5fsets_2dinter_2dcomm.Spec n
  eo__24eo_5fprog_5fsets_2dinter_2demp1 : eo__24eo_5fprog_5fsets_2dinter_2demp1.Spec n
  eo__24eo_5fprog_5fsets_2dinter_2demp2 : eo__24eo_5fprog_5fsets_2dinter_2demp2.Spec n
  eo__24eo_5fprog_5fsets_2dinter_2dmember : eo__24eo_5fprog_5fsets_2dinter_2dmember.Spec n
  eo__24eo_5fprog_5fsets_2dinter_2dself : eo__24eo_5fprog_5fsets_2dinter_2dself.Spec n
  eo__24eo_5fprog_5fsets_2dis_2dempty_2delim : eo__24eo_5fprog_5fsets_2dis_2dempty_2delim.Spec n
  eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim : eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim.Spec n
  eo__24eo_5fprog_5fsets_2dmember_2demp : eo__24eo_5fprog_5fsets_2dmember_2demp.Spec n
  eo__24eo_5fprog_5fsets_2dmember_2dsingleton : eo__24eo_5fprog_5fsets_2dmember_2dsingleton.Spec n
  eo__24eo_5fprog_5fsets_2dminus_2demp1 : eo__24eo_5fprog_5fsets_2dminus_2demp1.Spec n
  eo__24eo_5fprog_5fsets_2dminus_2demp2 : eo__24eo_5fprog_5fsets_2dminus_2demp2.Spec n
  eo__24eo_5fprog_5fsets_2dminus_2dmember : eo__24eo_5fprog_5fsets_2dminus_2dmember.Spec n
  eo__24eo_5fprog_5fsets_2dminus_2dself : eo__24eo_5fprog_5fsets_2dminus_2dself.Spec n
  eo__24eo_5fprog_5fsets_2dsubset_2delim : eo__24eo_5fprog_5fsets_2dsubset_2delim.Spec n
  eo__24eo_5fprog_5fsets_2dunion_2dcomm : eo__24eo_5fprog_5fsets_2dunion_2dcomm.Spec n
  eo__24eo_5fprog_5fsets_2dunion_2demp1 : eo__24eo_5fprog_5fsets_2dunion_2demp1.Spec n
  eo__24eo_5fprog_5fsets_2dunion_2demp2 : eo__24eo_5fprog_5fsets_2dunion_2demp2.Spec n
  eo__24eo_5fprog_5fsets_2dunion_2dmember : eo__24eo_5fprog_5fsets_2dunion_2dmember.Spec n
  eo__24eo_5fprog_5fsets_2dunion_2dself : eo__24eo_5fprog_5fsets_2dunion_2dself.Spec n
  eo__24eo_5fprog_5fsets_5fext : eo__24eo_5fprog_5fsets_5fext.Spec n
  eo__24eo_5fprog_5fsets_5fsingleton_5finj : eo__24eo_5fprog_5fsets_5fsingleton_5finj.Spec n
  eo__24eo_5fprog_5fskolem_5fintro : eo__24eo_5fprog_5fskolem_5fintro.Spec n
  eo__24eo_5fprog_5fsplit : eo__24eo_5fprog_5fsplit.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq : eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drefl : eo__24eo_5fprog_5fstr_2dcontains_2drefl.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt.Spec n
  eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1 : eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1.Spec n
  eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2 : eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2.Spec n
  eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse : eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange : eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc : eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen : eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv : eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv : eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv : eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv.Spec n
  eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d1 : eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d1.Spec n
  eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d2 : eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d2.Spec n
  eo__24eo_5fprog_5fstr_2dlt_2delim : eo__24eo_5fprog_5fstr_2dlt_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dprefixof_2deq : eo__24eo_5fprog_5fstr_2dprefixof_2deq.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dself : eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dself.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlen_2did : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlen_2did.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dall_2did : eo__24eo_5fprog_5fstr_2dreplace_2dall_2did.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn : eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse : eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2did : eo__24eo_5fprog_5fstr_2dreplace_2did.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains : eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dprefix : eo__24eo_5fprog_5fstr_2dreplace_2dprefix.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone : eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone : eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dself : eo__24eo_5fprog_5fstr_2dreplace_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp : eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dctn : eo__24eo_5fprog_5fstr_2dsubstr_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dctn_2dcontra : eo__24eo_5fprog_5fstr_2dsubstr_2dctn_2dcontra.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm : eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm.Spec n
  eo__24eo_5fprog_5fstr_2dsuffixof_2delim : eo__24eo_5fprog_5fstr_2dsuffixof_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dsuffixof_2deq : eo__24eo_5fprog_5fstr_2dsuffixof_2deq.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint : eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2didem : eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen : eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper : eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint : eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2didem : eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.Spec n
  eo__24eo_5fprog_5fstring_5fseq_5funit_5finj : eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.Spec n
  eo__24eo_5fprog_5fsymm : eo__24eo_5fprog_5fsymm.Spec n
  eo__24eo_5fprog_5ftrans : eo__24eo_5fprog_5ftrans.Spec n
  eo__24eo_5fprog_5ftrue_5felim : eo__24eo_5fprog_5ftrue_5felim.Spec n
  eo__24eo_5fprog_5ftrue_5fintro : eo__24eo_5fprog_5ftrue_5fintro.Spec n
  eo__24eo_5fprog_5ftrust : eo__24eo_5fprog_5ftrust.Spec n
  eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.Spec n
  eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat : eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.Spec n
  eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv : eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.Spec n
  eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv : eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.Spec n
  eo__24eo_5fprog_5fxor_5felim1 : eo__24eo_5fprog_5fxor_5felim1.Spec n
  eo__24eo_5fprog_5fxor_5felim2 : eo__24eo_5fprog_5fxor_5felim2.Spec n
  eo__24eo_5fpush_5fassume_5fcheck : eo__24eo_5fpush_5fassume_5fcheck.Spec n
  eo__24eo_5fpush_5finput_5fassume_5fcheck : eo__24eo_5fpush_5finput_5fassume_5fcheck.Spec n
  eo__24eo_5fpush_5fproven_5fcheck : eo__24eo_5fpush_5fproven_5fcheck.Spec n
  eo__24eo_5fstate_5fis_5fclosed : eo__24eo_5fstate_5fis_5fclosed.Spec n
  eo__24eo_5fstate_5fis_5frefutation : eo__24eo_5fstate_5fis_5frefutation.Spec n
  eo__24eo_5fstate_5fproven_5fnth : eo__24eo_5fstate_5fproven_5fnth.Spec n
  eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff : eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff.Spec n
  eo__24eo_5fto_5fsmt_5fnat : eo__24eo_5fto_5fsmt_5fnat.Spec n
  eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid : eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid.Spec n
  eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent : eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent.Spec n
  eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname : eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.Spec n
  eo__24eo_5fto_5fsmt_5fseq_2eempty : eo__24eo_5fto_5fsmt_5fseq_2eempty.Spec n
  eo__24eo_5fto_5fsmt_5fset_2eempty : eo__24eo_5fto_5fsmt_5fset_2eempty.Spec n
  eo__24eo_5fto_5fsmt_5fset_5felem_5ftype : eo__24eo_5fto_5fsmt_5fset_5felem_5ftype.Spec n
  eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff : eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff.Spec n
  eo__24eo_5fto_5fsmt_5ftester : eo__24eo_5fto_5fsmt_5ftester.Spec n
  eo__24eo_5fto_5fsmt_5ftuple_5fdecl : eo__24eo_5fto_5fsmt_5ftuple_5fdecl.Spec n
  eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec : eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec.Spec n
  eo__24eo_5ftypeof_5f_3d : eo__24eo_5ftypeof_5f_3d.Spec n
  eo__24eo_5ftypeof_5f_40_40Pair : eo__24eo_5ftypeof_5f_40_40Pair.Spec n
  eo__24eo_5ftypeof_5f_40_40TypedList_2econs : eo__24eo_5ftypeof_5f_40_40TypedList_2econs.Spec n
  eo__24eo_5ftypeof_5f_40_40TypedList_2enil : eo__24eo_5ftypeof_5f_40_40TypedList_2enil.Spec n
  eo__24eo_5ftypeof_5f_40_40aci_5fsorted : eo__24eo_5ftypeof_5f_40_40aci_5fsorted.Spec n
  eo__24eo_5ftypeof_5f_40_40mon : eo__24eo_5ftypeof_5f_40_40mon.Spec n
  eo__24eo_5ftypeof_5f_40_40pair : eo__24eo_5ftypeof_5f_40_40pair.Spec n
  eo__24eo_5ftypeof_5f_40_40poly : eo__24eo_5ftypeof_5f_40_40poly.Spec n
  eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff : eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff.Spec n
  eo__24eo_5ftypeof_5f_40bit : eo__24eo_5ftypeof_5f_40bit.Spec n
  eo__24eo_5ftypeof_5f_40bvsize : eo__24eo_5ftypeof_5f_40bvsize.Spec n
  eo__24eo_5ftypeof_5f_40const : eo__24eo_5ftypeof_5f_40const.Spec n
  eo__24eo_5ftypeof_5f_40div_5fby_5fzero : eo__24eo_5ftypeof_5f_40div_5fby_5fzero.Spec n
  eo__24eo_5ftypeof_5f_40purify : eo__24eo_5ftypeof_5f_40purify.Spec n
  eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent : eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent.Spec n
  eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff : eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff.Spec n
  eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff : eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff.Spec n
  eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre : eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre.Spec n
  eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult : eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult.Spec n
  eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult : eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult.Spec n
  eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult : eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult.Spec n
  eo__24eo_5ftypeof_5f_40witness_5fstring_5flength : eo__24eo_5ftypeof_5f_40witness_5fstring_5flength.Spec n
  eo__24eo_5ftypeof_5fBitVec : eo__24eo_5ftypeof_5fBitVec.Spec n
  eo__24eo_5ftypeof_5fSeq : eo__24eo_5ftypeof_5fSeq.Spec n
  eo__24eo_5ftypeof_5fapply : eo__24eo_5ftypeof_5fapply.Spec n
  eo__24eo_5ftypeof_5fbvand : eo__24eo_5ftypeof_5fbvand.Spec n
  eo__24eo_5ftypeof_5fbvnego : eo__24eo_5ftypeof_5fbvnego.Spec n
  eo__24eo_5ftypeof_5fbvnot : eo__24eo_5ftypeof_5fbvnot.Spec n
  eo__24eo_5ftypeof_5fbvult : eo__24eo_5ftypeof_5fbvult.Spec n
  eo__24eo_5ftypeof_5fdistinct : eo__24eo_5ftypeof_5fdistinct.Spec n
  eo__24eo_5ftypeof_5fdiv : eo__24eo_5ftypeof_5fdiv.Spec n
  eo__24eo_5ftypeof_5fdivisible : eo__24eo_5ftypeof_5fdivisible.Spec n
  eo__24eo_5ftypeof_5fdt_5fcons_5frec : eo__24eo_5ftypeof_5fdt_5fcons_5frec.Spec n
  eo__24eo_5ftypeof_5fdt_5fsel_5freturn : eo__24eo_5ftypeof_5fdt_5fsel_5freturn.Spec n
  eo__24eo_5ftypeof_5fforall : eo__24eo_5ftypeof_5fforall.Spec n
  eo__24eo_5ftypeof_5ffun_5ftype : eo__24eo_5ftypeof_5ffun_5ftype.Spec n
  eo__24eo_5ftypeof_5fint_2eispow2 : eo__24eo_5ftypeof_5fint_2eispow2.Spec n
  eo__24eo_5ftypeof_5fint_2epow2 : eo__24eo_5ftypeof_5fint_2epow2.Spec n
  eo__24eo_5ftypeof_5fis : eo__24eo_5ftypeof_5fis.Spec n
  eo__24eo_5ftypeof_5fis_5fint : eo__24eo_5ftypeof_5fis_5fint.Spec n
  eo__24eo_5ftypeof_5fite : eo__24eo_5ftypeof_5fite.Spec n
  eo__24eo_5ftypeof_5flambda : eo__24eo_5ftypeof_5flambda.Spec n
  eo__24eo_5ftypeof_5fnot : eo__24eo_5ftypeof_5fnot.Spec n
  eo__24eo_5ftypeof_5for : eo__24eo_5ftypeof_5for.Spec n
  eo__24eo_5ftypeof_5fre_2e_2a : eo__24eo_5ftypeof_5fre_2e_2a.Spec n
  eo__24eo_5ftypeof_5fre_2e_2b_2b : eo__24eo_5ftypeof_5fre_2e_2b_2b.Spec n
  eo__24eo_5ftypeof_5fre_2erange : eo__24eo_5ftypeof_5fre_2erange.Spec n
  eo__24eo_5ftypeof_5fselect : eo__24eo_5ftypeof_5fselect.Spec n
  eo__24eo_5ftypeof_5fseq_2eempty : eo__24eo_5ftypeof_5fseq_2eempty.Spec n
  eo__24eo_5ftypeof_5fseq_2enth : eo__24eo_5ftypeof_5fseq_2enth.Spec n
  eo__24eo_5ftypeof_5fseq_2eunit : eo__24eo_5ftypeof_5fseq_2eunit.Spec n
  eo__24eo_5ftypeof_5fset_2echoose : eo__24eo_5ftypeof_5fset_2echoose.Spec n
  eo__24eo_5ftypeof_5fset_2eempty : eo__24eo_5ftypeof_5fset_2eempty.Spec n
  eo__24eo_5ftypeof_5fset_2einsert : eo__24eo_5ftypeof_5fset_2einsert.Spec n
  eo__24eo_5ftypeof_5fset_2eis_5fempty : eo__24eo_5ftypeof_5fset_2eis_5fempty.Spec n
  eo__24eo_5ftypeof_5fset_2emember : eo__24eo_5ftypeof_5fset_2emember.Spec n
  eo__24eo_5ftypeof_5fset_2esingleton : eo__24eo_5ftypeof_5fset_2esingleton.Spec n
  eo__24eo_5ftypeof_5fset_2esubset : eo__24eo_5ftypeof_5fset_2esubset.Spec n
  eo__24eo_5ftypeof_5fset_2eunion : eo__24eo_5ftypeof_5fset_2eunion.Spec n
  eo__24eo_5ftypeof_5fstore : eo__24eo_5ftypeof_5fstore.Spec n
  eo__24eo_5ftypeof_5fstr_2e_2b_2b : eo__24eo_5ftypeof_5fstr_2e_2b_2b.Spec n
  eo__24eo_5ftypeof_5fstr_2e_3c : eo__24eo_5ftypeof_5fstr_2e_3c.Spec n
  eo__24eo_5ftypeof_5fstr_2eat : eo__24eo_5ftypeof_5fstr_2eat.Spec n
  eo__24eo_5ftypeof_5fstr_2econtains : eo__24eo_5ftypeof_5fstr_2econtains.Spec n
  eo__24eo_5ftypeof_5fstr_2efrom_5fcode : eo__24eo_5ftypeof_5fstr_2efrom_5fcode.Spec n
  eo__24eo_5ftypeof_5fstr_2ein_5fre : eo__24eo_5ftypeof_5fstr_2ein_5fre.Spec n
  eo__24eo_5ftypeof_5fstr_2eindexof : eo__24eo_5ftypeof_5fstr_2eindexof.Spec n
  eo__24eo_5ftypeof_5fstr_2eindexof_5fre : eo__24eo_5ftypeof_5fstr_2eindexof_5fre.Spec n
  eo__24eo_5ftypeof_5fstr_2eis_5fdigit : eo__24eo_5ftypeof_5fstr_2eis_5fdigit.Spec n
  eo__24eo_5ftypeof_5fstr_2elen : eo__24eo_5ftypeof_5fstr_2elen.Spec n
  eo__24eo_5ftypeof_5fstr_2ereplace : eo__24eo_5ftypeof_5fstr_2ereplace.Spec n
  eo__24eo_5ftypeof_5fstr_2ereplace_5fre : eo__24eo_5ftypeof_5fstr_2ereplace_5fre.Spec n
  eo__24eo_5ftypeof_5fstr_2erev : eo__24eo_5ftypeof_5fstr_2erev.Spec n
  eo__24eo_5ftypeof_5fstr_2esubstr : eo__24eo_5ftypeof_5fstr_2esubstr.Spec n
  eo__24eo_5ftypeof_5fstr_2eto_5fcode : eo__24eo_5ftypeof_5fstr_2eto_5fcode.Spec n
  eo__24eo_5ftypeof_5fstr_2eto_5flower : eo__24eo_5ftypeof_5fstr_2eto_5flower.Spec n
  eo__24eo_5ftypeof_5fstr_2eto_5fre : eo__24eo_5ftypeof_5fstr_2eto_5fre.Spec n
  eo__24eo_5ftypeof_5fstr_2eupdate : eo__24eo_5ftypeof_5fstr_2eupdate.Spec n
  eo__24eo_5ftypeof_5fto_5fint : eo__24eo_5ftypeof_5fto_5fint.Spec n
  eo__24eo_5ftypeof_5fto_5freal : eo__24eo_5ftypeof_5fto_5freal.Spec n
  eo__24eo_5ftypeof_5fupdate : eo__24eo_5ftypeof_5fupdate.Spec n
  eo__24from_5fclause : eo__24from_5fclause.Spec n
  eo__24get_5farg_5flist_5frec : eo__24get_5farg_5flist_5frec.Spec n
  eo__24get_5flambda_5ftype : eo__24get_5flambda_5ftype.Spec n
  eo__24get_5fvar_5ftype : eo__24get_5fvar_5ftype.Spec n
  eo__24is_5farith_5ftype : eo__24is_5farith_5ftype.Spec n
  eo__24is_5fseq_5fconst : eo__24is_5fseq_5fconst.Spec n
  eo__24is_5fseq_5fconst_5frec : eo__24is_5fseq_5fconst_5frec.Spec n
  eo__24lower_5fnot_5fand : eo__24lower_5fnot_5fand.Spec n
  eo__24mk_5farith_5fsum_5fub_5frec : eo__24mk_5farith_5fsum_5fub_5frec.Spec n
  eo__24mk_5farith_5ftrichotomy : eo__24mk_5farith_5ftrichotomy.Spec n
  eo__24mk_5fdistinct_5felim : eo__24mk_5fdistinct_5felim.Spec n
  eo__24mk_5fdistinct_5felim_5frec : eo__24mk_5fdistinct_5felim_5frec.Spec n
  eo__24mk_5fdt_5finst_5frec : eo__24mk_5fdt_5finst_5frec.Spec n
  eo__24mk_5fdt_5fsplit : eo__24mk_5fdt_5fsplit.Spec n
  eo__24mk_5fho_5fcong : eo__24mk_5fho_5fcong.Spec n
  eo__24mk_5fquant_5fminiscope_5fand : eo__24mk_5fquant_5fminiscope_5fand.Spec n
  eo__24mk_5fre_5fconcat : eo__24mk_5fre_5fconcat.Spec n
  eo__24mk_5fsymm : eo__24mk_5fsymm.Spec n
  eo__24mk_5ftrans : eo__24mk_5ftrans.Spec n
  eo__24pair_5ffirst : eo__24pair_5ffirst.Spec n
  eo__24pair_5fsecond : eo__24pair_5fsecond.Spec n
  eo__24re_5fsplit_5fstr_5fto_5fre : eo__24re_5fsplit_5fstr_5fto_5fre.Spec n
  eo__24seq_5felement_5fof_5funit : eo__24seq_5felement_5fof_5funit.Spec n
  eo__24seq_5fis_5fnon_5fempty : eo__24seq_5fis_5fnon_5fempty.Spec n
  eo__24smtx_5fdd_5fhas_5fdt : eo__24smtx_5fdd_5fhas_5fdt.Spec n
  eo__24smtx_5fdd_5flookup : eo__24smtx_5fdd_5flookup.Spec n
  eo__24smtx_5fdecl_5finhabited : eo__24smtx_5fdecl_5finhabited.Spec n
  eo__24smtx_5fdecl_5fwf_5frec : eo__24smtx_5fdecl_5fwf_5frec.Spec n
  eo__24smtx_5fdt_5fcons_5finhabited : eo__24smtx_5fdt_5fcons_5finhabited.Spec n
  eo__24smtx_5fdt_5fcons_5fwf_5frec : eo__24smtx_5fdt_5fcons_5fwf_5frec.Spec n
  eo__24smtx_5fdt_5finhabited : eo__24smtx_5fdt_5finhabited.Spec n
  eo__24smtx_5fdt_5fresolve : eo__24smtx_5fdt_5fresolve.Spec n
  eo__24smtx_5fdt_5fwf_5frec : eo__24smtx_5fdt_5fwf_5frec.Spec n
  eo__24smtx_5fdtc_5fnum_5fsels : eo__24smtx_5fdtc_5fnum_5fsels.Spec n
  eo__24smtx_5fdtc_5fresolve : eo__24smtx_5fdtc_5fresolve.Spec n
  eo__24smtx_5finhabited_5ftype : eo__24smtx_5finhabited_5ftype.Spec n
  eo__24smtx_5fret_5ftypeof_5fsel : eo__24smtx_5fret_5ftypeof_5fsel.Spec n
  eo__24smtx_5fret_5ftypeof_5fsel_5frec : eo__24smtx_5fret_5ftypeof_5fsel_5frec.Spec n
  eo__24smtx_5ftype_5fwf : eo__24smtx_5ftype_5fwf.Spec n
  eo__24smtx_5ftype_5fwf_5fcomponent : eo__24smtx_5ftype_5fwf_5fcomponent.Spec n
  eo__24smtx_5ftype_5fwf_5frec : eo__24smtx_5ftype_5fwf_5frec.Spec n
  eo__24smtx_5ftypeof_5f_3d : eo__24smtx_5ftypeof_5f_3d.Spec n
  eo__24smtx_5ftypeof_5fapply : eo__24smtx_5ftypeof_5fapply.Spec n
  eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 : eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1.Spec n
  eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 : eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2.Spec n
  eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret : eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret.Spec n
  eo__24smtx_5ftypeof_5fbv_5fop_5f1 : eo__24smtx_5ftypeof_5fbv_5fop_5f1.Spec n
  eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret : eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret.Spec n
  eo__24smtx_5ftypeof_5fdt_5fcons_5frec : eo__24smtx_5ftypeof_5fdt_5fcons_5frec.Spec n
  eo__24smtx_5ftypeof_5fguard : eo__24smtx_5ftypeof_5fguard.Spec n
  eo__24smtx_5ftypeof_5fguard_5fwf : eo__24smtx_5ftypeof_5fguard_5fwf.Spec n
  eo__24smtx_5ftypeof_5fint_5fto_5fbv : eo__24smtx_5ftypeof_5fint_5fto_5fbv.Spec n
  eo__24smtx_5ftypeof_5fite : eo__24smtx_5ftypeof_5fite.Spec n
  eo__24smtx_5ftypeof_5fmap_5fdiff : eo__24smtx_5ftypeof_5fmap_5fdiff.Spec n
  eo__24smtx_5ftypeof_5fre_2e_5e : eo__24smtx_5ftypeof_5fre_2e_5e.Spec n
  eo__24smtx_5ftypeof_5fre_2eloop : eo__24smtx_5ftypeof_5fre_2eloop.Spec n
  eo__24smtx_5ftypeof_5frotate_5fleft : eo__24smtx_5ftypeof_5frotate_5fleft.Spec n
  eo__24smtx_5ftypeof_5frotate_5fright : eo__24smtx_5ftypeof_5frotate_5fright.Spec n
  eo__24smtx_5ftypeof_5fselect : eo__24smtx_5ftypeof_5fselect.Spec n
  eo__24smtx_5ftypeof_5fseq_2enth : eo__24smtx_5ftypeof_5fseq_2enth.Spec n
  eo__24smtx_5ftypeof_5fseq_5fdiff : eo__24smtx_5ftypeof_5fseq_5fdiff.Spec n
  eo__24smtx_5ftypeof_5fseq_5fop_5f1 : eo__24smtx_5ftypeof_5fseq_5fop_5f1.Spec n
  eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret : eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret.Spec n
  eo__24smtx_5ftypeof_5fseq_5fop_5f2 : eo__24smtx_5ftypeof_5fseq_5fop_5f2.Spec n
  eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret : eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret.Spec n
  eo__24smtx_5ftypeof_5fseq_5fop_5f3 : eo__24smtx_5ftypeof_5fseq_5fop_5f3.Spec n
  eo__24smtx_5ftypeof_5fset_2emember : eo__24smtx_5ftypeof_5fset_2emember.Spec n
  eo__24smtx_5ftypeof_5fsets_5fop_5f2 : eo__24smtx_5ftypeof_5fsets_5fop_5f2.Spec n
  eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret : eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret.Spec n
  eo__24smtx_5ftypeof_5fstore : eo__24smtx_5ftypeof_5fstore.Spec n
  eo__24smtx_5ftypeof_5fstr_2eat : eo__24smtx_5ftypeof_5fstr_2eat.Spec n
  eo__24smtx_5ftypeof_5fstr_2eindexof : eo__24smtx_5ftypeof_5fstr_2eindexof.Spec n
  eo__24smtx_5ftypeof_5fstr_2esubstr : eo__24smtx_5ftypeof_5fstr_2esubstr.Spec n
  eo__24smtx_5ftypeof_5fstr_2eupdate : eo__24smtx_5ftypeof_5fstr_2eupdate.Spec n
  eo__24str_5fmembership_5fre : eo__24str_5fmembership_5fre.Spec n
  eo__24str_5fmembership_5fstr : eo__24str_5fmembership_5fstr.Spec n
  eo__24to_5fclause : eo__24to_5fclause.Spec n
  eo__24to_5fcube : eo__24to_5fcube.Spec n
  eo__24tuple_5farg_5flist : eo__24tuple_5farg_5flist.Spec n
  eo__24typed_5flist_5felement_5ftype : eo__24typed_5flist_5felement_5ftype.Spec n

end pathos_compiled_checker
