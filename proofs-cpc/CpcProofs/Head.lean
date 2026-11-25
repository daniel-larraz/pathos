module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtTranslate
import all Cpc.SmtTranslate
public import Cpc.SmtModel
import all Cpc.SmtModel
public import CpcCases
import all CpcCases
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

/-- What is proved of `$abconv_int_to_bv_elim`. -/
def eo__24abconv_5fint_5fto_5fbv_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24abconv_5fint_5fto_5fbv_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__abconv_int_to_bv_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$abconv_ubv_to_int_elim`. -/
def eo__24abconv_5fubv_5fto_5fint_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24abconv_5fubv_5fto_5fint_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__abconv_ubv_to_int_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$arith_mk_one`. -/
def eo__24arith_5fmk_5fone.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24arith_5fmk_5fone s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_mk_one x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$arith_mk_zero`. -/
def eo__24arith_5fmk_5fzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24arith_5fmk_5fzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_mk_zero x_a0)
      | core.result.Result.Err _ => True ⦄div

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

/-- What is proved of `$assoc_nil_nth`. -/
def eo__24assoc_5fnil_5fnth.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_apply_binary`. -/
def eo__24bv_5fbitblast_5fapply_5fbinary.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fapply_5fbinary s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_binary x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_apply_ite`. -/
def eo__24bv_5fbitblast_5fapply_5fite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fapply_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_apply_unary`. -/
def eo__24bv_5fbitblast_5fapply_5funary.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24bv_5fbitblast_5fapply_5funary s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_unary x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_binary_app`. -/
def eo__24bv_5fbitblast_5fbinary_5fapp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_binary_app x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_concat`. -/
def eo__24bv_5fbitblast_5fconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24bv_5fbitblast_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_head`. -/
def eo__24bv_5fbitblast_5fhead.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fbitblast_5fhead s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_head x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_prefix`. -/
def eo__24bv_5fbitblast_5fprefix.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_prefix x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_slt_impl`. -/
def eo__24bv_5fbitblast_5fslt_5fimpl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fslt_5fimpl s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_slt_impl x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_subsequence`. -/
def eo__24bv_5fbitblast_5fsubsequence.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_tail`. -/
def eo__24bv_5fbitblast_5ftail.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fbitblast_5ftail s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_tail x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_ult`. -/
def eo__24bv_5fbitblast_5fult.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fult s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitblast_ult_rec`. -/
def eo__24bv_5fbitblast_5fult_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_bitwidth`. -/
def eo__24bv_5fbitwidth.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fbitwidth s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitwidth x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_get_first_const_child`. -/
def eo__24bv_5fget_5ffirst_5fconst_5fchild.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fget_5ffirst_5fconst_5fchild s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_get_first_const_child x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_mk_bitblast_step_add`. -/
def eo__24bv_5fmk_5fbitblast_5fstep_5fadd.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24bv_5fmk_5fbitblast_5fstep_5fadd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_add x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_mk_bitblast_step_concat`. -/
def eo__24bv_5fmk_5fbitblast_5fstep_5fconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24bv_5fmk_5fbitblast_5fstep_5fconcat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_concat x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_mk_bitblast_step_eq_rec`. -/
def eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_eq_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_mk_bitblast_step_ite`. -/
def eo__24bv_5fmk_5fbitblast_5fstep_5fite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24bv_5fmk_5fbitblast_5fstep_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_mk_bitblast_step_var_rec`. -/
def eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_var_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$bv_ripple_carry_adder_2`. -/
def eo__24bv_5fripple_5fcarry_5fadder_5f2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24bv_5fripple_5fcarry_5fadder_5f2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_ripple_carry_adder_2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$chain_m_resolve`. -/
def eo__24chain_5fm_5fresolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24chain_5fm_5fresolve s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$chain_m_resolve_final`. -/
def eo__24chain_5fm_5fresolve_5ffinal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24chain_5fm_5fresolve_5ffinal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve_final x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$chain_m_resolve_rec`. -/
def eo__24chain_5fm_5fresolve_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24chain_5fm_5fresolve_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$chain_m_resolve_rec_step`. -/
def eo__24chain_5fm_5fresolve_5frec_5fstep.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24chain_5fm_5fresolve_5frec_5fstep s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve_rec_step x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$compute_card`. -/
def eo__24compute_5fcard.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24compute_5fcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__compute_card x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$dt_arg_list`. -/
def eo__24dt_5farg_5flist.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_arg_list x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$dt_collapse_updater_rhs`. -/
def eo__24dt_5fcollapse_5fupdater_5frhs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24dt_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_collapse_updater_rhs x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_is_list_nil`. -/
def eo__24eo_5fis_5flist_5fnil.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_*`. -/
def eo__24eo_5fis_5flist_5fnil_5f_2a.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5f_2a s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_mult x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_+`. -/
def eo__24eo_5fis_5flist_5fnil_5f_2b.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5f_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_plus x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_@@TypedList.cons`. -/
def eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil__at__at_TypedList_cons x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_bvadd`. -/
def eo__24eo_5fis_5flist_5fnil_5fbvadd.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5fbvadd s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvadd x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_bvand`. -/
def eo__24eo_5fis_5flist_5fnil_5fbvand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5fbvand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvand x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_bvmul`. -/
def eo__24eo_5fis_5flist_5fnil_5fbvmul.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5fbvmul s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvmul x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_bvor`. -/
def eo__24eo_5fis_5flist_5fnil_5fbvor.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5fbvor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvor x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_bvxor`. -/
def eo__24eo_5fis_5flist_5fnil_5fbvxor.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5fbvxor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvxor x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil_str.++`. -/
def eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_str_concat x_a0)
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

/-- What is proved of `$eo_nil`. -/
def eo__24eo_5fnil.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_*`. -/
def eo__24eo_5fnil_5f_2a.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5f_2a s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_mult x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_+`. -/
def eo__24eo_5fnil_5f_2b.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5f_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_plus x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_@@TypedList.cons`. -/
def eo__24eo_5fnil_5f_40_40TypedList_2econs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil__at__at_TypedList_cons x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_bvadd`. -/
def eo__24eo_5fnil_5fbvadd.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5fbvadd s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_bvadd x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_bvand`. -/
def eo__24eo_5fnil_5fbvand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5fbvand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_bvand x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_bvmul`. -/
def eo__24eo_5fnil_5fbvmul.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5fbvmul s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_bvmul x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_bvor`. -/
def eo__24eo_5fnil_5fbvor.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5fbvor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_bvor x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_bvxor`. -/
def eo__24eo_5fnil_5fbvxor.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5fbvxor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_bvxor x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil_str.++`. -/
def eo__24eo_5fnil_5fstr_2e_2b_2b.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fnil_5fstr_2e_2b_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_str_concat x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_and_elim`. -/
def eo__24eo_5fprog_5fand_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fand_5felim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_and_elim x_a0 x_a1)
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

/-- What is proved of `$eo_prog_arith-abs-int-gt`. -/
def eo__24eo_5fprog_5farith_2dabs_2dint_2dgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dabs_2dint_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_abs_int_gt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-abs-real-gt`. -/
def eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_abs_real_gt x_a0 x_a1)
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

/-- What is proved of `$eo_prog_arith-div-total-zero-int`. -/
def eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_div_total_zero_int x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-div-total-zero-real`. -/
def eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_div_total_zero_real x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-divisible-elim`. -/
def eo__24eo_5fprog_5farith_2ddivisible_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2ddivisible_2delim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_divisible_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-elim-gt`. -/
def eo__24eo_5fprog_5farith_2delim_2dgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2delim_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_gt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-elim-int-gt`. -/
def eo__24eo_5fprog_5farith_2delim_2dint_2dgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2delim_2dint_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_int_gt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-elim-int-lt`. -/
def eo__24eo_5fprog_5farith_2delim_2dint_2dlt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2delim_2dint_2dlt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_int_lt x_a0 x_a1)
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

/-- What is proved of `$eo_prog_arith-geq-norm1-int`. -/
def eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_geq_norm1_int x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-geq-norm1-real`. -/
def eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_geq_norm1_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-geq-tighten`. -/
def eo__24eo_5fprog_5farith_2dgeq_2dtighten.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dgeq_2dtighten s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_geq_tighten x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-div-total`. -/
def eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_div_total x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-div-total-neg`. -/
def eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_div_total_neg x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-div-total-one`. -/
def eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_div_total_one x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-div-total-over-mod`. -/
def eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_div_total_over_mod x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-div-total-zero`. -/
def eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_div_total_zero x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-eq-conflict`. -/
def eo__24eo_5fprog_5farith_2dint_2deq_2dconflict.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2dint_2deq_2dconflict s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_eq_conflict x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-mod-total`. -/
def eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_mod_total x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-mod-total-neg`. -/
def eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_mod_total_neg x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-mod-total-one`. -/
def eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_mod_total_one x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_arith-int-mod-total-zero`. -/
def eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_int_mod_total_zero x_a0)
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

/-- What is proved of `$eo_prog_arith-leq-norm`. -/
def eo__24eo_5fprog_5farith_2dleq_2dnorm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5farith_2dleq_2dnorm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_leq_norm x_a0 x_a1)
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

/-- What is proved of `$eo_prog_arith-mod-over-mod-1`. -/
def eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_mod_over_mod_1 x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_prog_arrays_read_over_write_contra`. -/
def eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arrays_read_over_write_contra x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-and-conf`. -/
def eo__24eo_5fprog_5fbool_2dand_2dconf.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbool_2dand_2dconf s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_and_conf x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-and-conf2`. -/
def eo__24eo_5fprog_5fbool_2dand_2dconf2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbool_2dand_2dconf2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_and_conf2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-and-de-morgan`. -/
def eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_and_de_morgan x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_prog_bool-implies-or-distrib`. -/
def eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_implies_or_distrib x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_prog_bool-or-and-distrib`. -/
def eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_or_and_distrib x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-or-de-morgan`. -/
def eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_or_de_morgan x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-or-taut`. -/
def eo__24eo_5fprog_5fbool_2dor_2dtaut.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbool_2dor_2dtaut s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_or_taut x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bool-or-taut2`. -/
def eo__24eo_5fprog_5fbool_2dor_2dtaut2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbool_2dor_2dtaut2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bool_or_taut2 x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_prog_bv-ashr-by-const-0`. -/
def eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ashr_by_const_0 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ashr-by-const-1`. -/
def eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ashr_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ashr-by-const-2`. -/
def eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 → Represents.rep s a8 x_a8 →
    eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ashr_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ashr-zero`. -/
def eo__24eo_5fprog_5fbv_2dashr_2dzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dashr_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ashr_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-commutative-comp`. -/
def eo__24eo_5fprog_5fbv_2dcommutative_2dcomp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dcommutative_2dcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_commutative_comp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-comp-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dcomp_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dcomp_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_comp_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-eq-extract-elim2`. -/
def eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 →
    eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_eq_extract_elim2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-eq-extract-elim3`. -/
def eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 →
    eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_eq_extract_elim3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-eq-not-solve`. -/
def eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_eq_not_solve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-extract-concat-1`. -/
def eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_concat_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-extract-extract`. -/
def eo__24eo_5fprog_5fbv_2dextract_2dextract.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 → Represents.rep s a8 x_a8 →
    eo__24eo_5fprog_5fbv_2dextract_2dextract s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_extract x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
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

/-- What is proved of `$eo_prog_bv-extract-sign-extend-3`. -/
def eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 → Represents.rep s a8 x_a8 →
    eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_sign_extend_3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-extract-whole`. -/
def eo__24eo_5fprog_5fbv_2dextract_2dwhole.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2dextract_2dwhole s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_whole x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-const-children-1`. -/
def eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_children_1 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-const-children-2`. -/
def eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_children_2 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-const-cond-1`. -/
def eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_cond_1 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-const-cond-2`. -/
def eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_cond_2 x_a0 x_a1)
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

/-- What is proved of `$eo_prog_bv-ite-merge-else-else`. -/
def eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_else_else x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-merge-else-if`. -/
def eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_else_if x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-merge-then-else`. -/
def eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_then_else x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-merge-then-if`. -/
def eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_then_if x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-width-one`. -/
def eo__24eo_5fprog_5fbv_2dite_2dwidth_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dite_2dwidth_2done s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_width_one x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ite-width-one-not`. -/
def eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_width_one_not x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-lshr-by-const-0`. -/
def eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_0 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-lshr-by-const-1`. -/
def eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-lshr-by-const-2`. -/
def eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-lshr-zero`. -/
def eo__24eo_5fprog_5fbv_2dlshr_2dzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dlshr_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-lt-self`. -/
def eo__24eo_5fprog_5fbv_2dlt_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dlt_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lt_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-merge-sign-extend-1`. -/
def eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_merge_sign_extend_1 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-merge-sign-extend-2`. -/
def eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_merge_sign_extend_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-nego-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dnego_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2dnego_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_nego_eliminate x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-not-idemp`. -/
def eo__24eo_5fprog_5fbv_2dnot_2didemp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dnot_2didemp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_idemp x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-not-neq`. -/
def eo__24eo_5fprog_5fbv_2dnot_2dneq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dnot_2dneq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_neq x_a0 x_a1)
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

/-- What is proved of `$eo_prog_bv-redand-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dredand_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2dredand_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_redand_eliminate x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-redor-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dredor_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2dredor_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_redor_eliminate x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-rotate-left-eliminate-2`. -/
def eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_rotate_left_eliminate_2 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-rotate-right-eliminate-2`. -/
def eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_rotate_right_eliminate_2 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-sdivo-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dsdivo_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fbv_2dsdivo_2deliminate s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sdivo_eliminate x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
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

/-- What is proved of `$eo_prog_bv-shl-by-const-0`. -/
def eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_by_const_0 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-shl-by-const-1`. -/
def eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-shl-by-const-2`. -/
def eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 →
    eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-shl-zero`. -/
def eo__24eo_5fprog_5fbv_2dshl_2dzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dshl_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-sign-extend-eliminate-0`. -/
def eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sign_extend_eliminate_0 x_a0)
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

/-- What is proved of `$eo_prog_bv-srem-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dsrem_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dsrem_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_srem_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-udiv-one`. -/
def eo__24eo_5fprog_5fbv_2dudiv_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dudiv_2done s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_one x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-udiv-pow2-not-one`. -/
def eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 → Represents.rep s a8 x_a8 →
    eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-udiv-zero`. -/
def eo__24eo_5fprog_5fbv_2dudiv_2dzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dudiv_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_zero x_a0 x_a1)
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

/-- What is proved of `$eo_prog_bv-ugt-urem`. -/
def eo__24eo_5fprog_5fbv_2dugt_2durem.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dugt_2durem s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ugt_urem x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ule-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dule_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dule_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ule-max`. -/
def eo__24eo_5fprog_5fbv_2dule_2dmax.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fbv_2dule_2dmax s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_max x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ule-self`. -/
def eo__24eo_5fprog_5fbv_2dule_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dule_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ule-zero`. -/
def eo__24eo_5fprog_5fbv_2dule_2dzero.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dule_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ult-one`. -/
def eo__24eo_5fprog_5fbv_2dult_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2dult_2done s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ult_one x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ult-self`. -/
def eo__24eo_5fprog_5fbv_2dult_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dult_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ult_self x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ult-zero-1`. -/
def eo__24eo_5fprog_5fbv_2dult_2dzero_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dult_2dzero_2d1 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ult_zero_1 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-ult-zero-2`. -/
def eo__24eo_5fprog_5fbv_2dult_2dzero_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dult_2dzero_2d2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ult_zero_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-urem-one`. -/
def eo__24eo_5fprog_5fbv_2durem_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2durem_2done s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_urem_one x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-urem-pow2-not-one`. -/
def eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 → Represents.rep s a8 x_a8 →
    eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_urem_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-urem-self`. -/
def eo__24eo_5fprog_5fbv_2durem_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fbv_2durem_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_urem_self x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-usubo-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dusubo_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fbv_2dusubo_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_usubo_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-zero-extend-eliminate`. -/
def eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_zero_extend_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-zero-extend-eliminate-0`. -/
def eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_zero_extend_eliminate_0 x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-zero-extend-eq-const-1`. -/
def eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 →
    eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_zero_extend_eq_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-zero-extend-eq-const-2`. -/
def eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 →
    eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_zero_extend_eq_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv-zero-ule`. -/
def eo__24eo_5fprog_5fbv_2dzero_2dule.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_2dzero_2dule s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_zero_ule x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_bv_poly_norm_eq`. -/
def eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_poly_norm_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_chain_m_resolution`. -/
def eo__24eo_5fprog_5fchain_5fm_5fresolution.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fchain_5fm_5fresolution s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_chain_m_resolution x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_chain_resolution`. -/
def eo__24eo_5fprog_5fchain_5fresolution.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fchain_5fresolution s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_chain_resolution x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_and_neg`. -/
def eo__24eo_5fprog_5fcnf_5fand_5fneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fcnf_5fand_5fneg s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_and_neg x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_cnf_and_pos`. -/
def eo__24eo_5fprog_5fcnf_5fand_5fpos.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fcnf_5fand_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_and_pos x_a0 x_a1)
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

/-- What is proved of `$eo_prog_cnf_or_neg`. -/
def eo__24eo_5fprog_5fcnf_5for_5fneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fcnf_5for_5fneg s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_or_neg x_a0 x_a1)
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

/-- What is proved of `$eo_prog_cong`. -/
def eo__24eo_5fprog_5fcong.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cong x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_contra`. -/
def eo__24eo_5fprog_5fcontra.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_contra x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_distinct-elim`. -/
def eo__24eo_5fprog_5fdistinct_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fdistinct_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_distinct-false`. -/
def eo__24eo_5fprog_5fdistinct_2dfalse.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fdistinct_2dfalse s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_false x_a0)
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

/-- What is proved of `$eo_prog_exists_string_length`. -/
def eo__24eo_5fprog_5fexists_5fstring_5flength.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fexists_5fstring_5flength s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_exists_string_length x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_factoring`. -/
def eo__24eo_5fprog_5ffactoring.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5ffactoring s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_factoring x_a0)
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

/-- What is proved of `$eo_prog_int_tight_lb`. -/
def eo__24eo_5fprog_5fint_5ftight_5flb.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fint_5ftight_5flb s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_int_tight_lb x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_int_tight_ub`. -/
def eo__24eo_5fprog_5fint_5ftight_5fub.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fint_5ftight_5fub s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_int_tight_ub x_a0)
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

/-- What is proved of `$eo_prog_nary_cong`. -/
def eo__24eo_5fprog_5fnary_5fcong.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fnary_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_nary_cong x_a0 x_a1)
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

/-- What is proved of `$eo_prog_not_or_elim`. -/
def eo__24eo_5fprog_5fnot_5for_5felim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fnot_5for_5felim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_or_elim x_a0 x_a1)
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

/-- What is proved of `$eo_prog_pairwise_cong`. -/
def eo__24eo_5fprog_5fpairwise_5fcong.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fpairwise_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_pairwise_cong x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_process_scope`. -/
def eo__24eo_5fprog_5fprocess_5fscope.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_process_scope x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_quant-merge-prenex`. -/
def eo__24eo_5fprog_5fquant_2dmerge_2dprenex.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fquant_2dmerge_2dprenex s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_merge_prenex x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_quant-miniscope-and`. -/
def eo__24eo_5fprog_5fquant_2dminiscope_2dand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fquant_2dminiscope_2dand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_miniscope_and x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-concat-merge`. -/
def eo__24eo_5fprog_5fre_2dconcat_2dmerge.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fre_2dconcat_2dmerge s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat_merge x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-concat-star-repeat`. -/
def eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat_star_repeat x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-concat-star-swap`. -/
def eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat_star_swap x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_prog_re-in-sigma`. -/
def eo__24eo_5fprog_5fre_2din_2dsigma.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_2din_2dsigma s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_sigma x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-in-sigma-star`. -/
def eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_sigma_star x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-inter-all`. -/
def eo__24eo_5fprog_5fre_2dinter_2dall.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2dinter_2dall s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_inter_all x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-inter-cstring`. -/
def eo__24eo_5fprog_5fre_2dinter_2dcstring.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fre_2dinter_2dcstring s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_inter_cstring x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-inter-cstring-neg`. -/
def eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_inter_cstring_neg x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-loop-neg`. -/
def eo__24eo_5fprog_5fre_2dloop_2dneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fre_2dloop_2dneg s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_loop_neg x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-loop-star`. -/
def eo__24eo_5fprog_5fre_2dloop_2dstar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fre_2dloop_2dstar s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_loop_star x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-opt-elim`. -/
def eo__24eo_5fprog_5fre_2dopt_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_2dopt_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_opt_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-plus-elim`. -/
def eo__24eo_5fprog_5fre_2dplus_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_2dplus_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_plus_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-range-emp`. -/
def eo__24eo_5fprog_5fre_2drange_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fre_2drange_2demp s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_range_emp x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-range-non-singleton-1`. -/
def eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_range_non_singleton_1 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-range-non-singleton-2`. -/
def eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_range_non_singleton_2 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-range-refl`. -/
def eo__24eo_5fprog_5fre_2drange_2drefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2drange_2drefl s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_range_refl x_a0 x_a1)
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

/-- What is proved of `$eo_prog_re-star-union-char`. -/
def eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_star_union_char x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-star-union-drop-emp`. -/
def eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_star_union_drop_emp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-union-all`. -/
def eo__24eo_5fprog_5fre_2dunion_2dall.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_2dunion_2dall s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_union_all x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re-union-const-elim`. -/
def eo__24eo_5fprog_5fre_2dunion_2dconst_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fre_2dunion_2dconst_2delim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_union_const_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re_concat`. -/
def eo__24eo_5fprog_5fre_5fconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_5fconcat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re_inter`. -/
def eo__24eo_5fprog_5fre_5finter.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_5finter s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_inter x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re_unfold_neg_concat_fixed`. -/
def eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_unfold_neg_concat_fixed x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_re_unfold_pos`. -/
def eo__24eo_5fprog_5fre_5funfold_5fpos.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fre_5funfold_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_unfold_pos x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_refl`. -/
def eo__24eo_5fprog_5frefl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5frefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_refl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_reordering`. -/
def eo__24eo_5fprog_5freordering.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5freordering s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_reordering x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_resolution`. -/
def eo__24eo_5fprog_5fresolution.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fresolution s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_resolution x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_prog_seq-len-unit`. -/
def eo__24eo_5fprog_5fseq_2dlen_2dunit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fseq_2dlen_2dunit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_seq_len_unit x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_seq-nth-concat-unit`. -/
def eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_seq_nth_concat_unit x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_seq-nth-unit`. -/
def eo__24eo_5fprog_5fseq_2dnth_2dunit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fseq_2dnth_2dunit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_seq_nth_unit x_a0)
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

/-- What is proved of `$eo_prog_str-at-elim`. -/
def eo__24eo_5fprog_5fstr_2dat_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dat_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_at_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-concat-clash`. -/
def eo__24eo_5fprog_5fstr_2dconcat_2dclash.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dconcat_2dclash s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_clash x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-concat-clash2`. -/
def eo__24eo_5fprog_5fstr_2dconcat_2dclash2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dconcat_2dclash2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_clash2 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-concat-unify`. -/
def eo__24eo_5fprog_5fstr_2dconcat_2dunify.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dconcat_2dunify s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_unify x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-concat-unify-base`. -/
def eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_unify_base x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-char`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2dchar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dcontains_2dchar s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_char x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-emp`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dcontains_2demp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_emp x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_prog_str-contains-repl-char`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_char x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-repl-self`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-repl-self-tgt-char`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_self_tgt_char x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-repl-tgt`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_tgt x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-contains-split-char`. -/
def eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_split_char x_a0 x_a1 x_a2 x_a3 x_a4)
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

/-- What is proved of `$eo_prog_str-eq-repl-emp-tgt-nemp`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_emp_tgt_nemp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-repl-len-one-emp-prefix`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_len_one_emp_prefix x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-repl-nemp-src-emp`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_nemp_src_emp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-repl-no-change`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_no_change x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-eq-repl-self-emp`. -/
def eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_self_emp x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_prog_str-from-int-no-ctn-nondigit`. -/
def eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_from_int_no_ctn_nondigit x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-in-re-contains`. -/
def eo__24eo_5fprog_5fstr_2din_2dre_2dcontains.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2din_2dre_2dcontains s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_contains x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-in-re-from-int-dig-range`. -/
def eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_from_int_dig_range x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-in-re-from-int-nemp-dig-range`. -/
def eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_from_int_nemp_dig_range x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-in-re-inter-elim`. -/
def eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_inter_elim x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-in-re-range-elim`. -/
def eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_range_elim x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-in-re-union-elim`. -/
def eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_union_elim x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-contains-pre`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dcontains_2dpre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dindexof_2dcontains_2dpre s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_contains_pre x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-find-emp`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dfind_2demp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dindexof_2dfind_2demp s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_find_emp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-len-oob`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 →
    eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_len_oob x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-len-oob2`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 →
    eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob2 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_len_oob2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-no-contains`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dno_2dcontains.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dindexof_2dno_2dcontains s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_no_contains x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-oob`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2doob.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dindexof_2doob s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_oob x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-oob2`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2doob2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dindexof_2doob2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_oob2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-re-emp-re`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dre_2demp_2dre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dindexof_2dre_2demp_2dre s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_re_emp_re x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-re-none`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dre_2dnone.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dindexof_2dre_2dnone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_re_none x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-indexof-self`. -/
def eo__24eo_5fprog_5fstr_2dindexof_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dindexof_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_indexof_self x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-is-digit-elim`. -/
def eo__24eo_5fprog_5fstr_2dis_2ddigit_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dis_2ddigit_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_is_digit_elim x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-len-concat-rec`. -/
def eo__24eo_5fprog_5fstr_2dlen_2dconcat_2drec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dlen_2dconcat_2drec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_len_concat_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-len-eq-zero-base`. -/
def eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dbase.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dbase s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_len_eq_zero_base x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-len-eq-zero-concat-rec`. -/
def eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dconcat_2drec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dconcat_2drec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_len_eq_zero_concat_rec x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_prog_str-len-substr-in-range`. -/
def eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_len_substr_in_range x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
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

/-- What is proved of `$eo_prog_str-leq-empty`. -/
def eo__24eo_5fprog_5fstr_2dleq_2dempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dleq_2dempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_leq_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-leq-empty-eq`. -/
def eo__24eo_5fprog_5fstr_2dleq_2dempty_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstr_2dleq_2dempty_2deq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_leq_empty_eq x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-lt-elim`. -/
def eo__24eo_5fprog_5fstr_2dlt_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dlt_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_lt_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-prefixof-elim`. -/
def eo__24eo_5fprog_5fstr_2dprefixof_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstr_2dprefixof_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_prefixof_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-prefixof-eq`. -/
def eo__24eo_5fprog_5fstr_2dprefixof_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dprefixof_2deq s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_prefixof_eq x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-prefixof-one`. -/
def eo__24eo_5fprog_5fstr_2dprefixof_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dprefixof_2done s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_prefixof_one x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-dual-ite1`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_dual_ite1 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-repl-repl-dual-ite2`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite2 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_dual_ite2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
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

/-- What is proved of `$eo_prog_str-repl-repl-lookahead-id-simp`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_lookahead_id_simp x_a0 x_a1 x_a2 x_a3 x_a4)
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

/-- What is proved of `$eo_prog_str-repl-repl-src-inv-no-ctn3`. -/
def eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 →
    eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
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

/-- What is proved of `$eo_prog_str-replace-all-empty`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_empty x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_prog_str-replace-all-self`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_self x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_prog_str-replace-emp-ctn-src`. -/
def eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_emp_ctn_src x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_prog_str-substr-char-start-eq-len`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_char_start_eq_len x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-combine1`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_combine1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-combine2`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 → Represents.rep s a7 x_a7 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_combine2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-concat1`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_concat1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-concat2`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dconcat2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dconcat2 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_concat2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
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

/-- What is proved of `$eo_prog_str-substr-empty-range`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_empty_range x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-empty-start`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_empty_start x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-empty-start-neg`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_empty_start_neg x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-empty-str`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_empty_str x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-eq-empty`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 →
    eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_eq_empty x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-eq-empty-leq-len`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 →
    eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_eq_empty_leq_len x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-full`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dfull.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dfull s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_full x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-full-eq`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dfull_2deq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dfull_2deq s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_full_eq x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-len-include`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_len_include x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-len-norm`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_len_norm x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-replace`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dreplace.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dreplace s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_replace x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-substr-start-geq-len`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 → Represents.rep s a6 x_a6 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_substr_start_geq_len x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-substr-z-eq-empty-leq`. -/
def eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_z_eq_empty_leq x_a0 x_a1 x_a2 x_a3 x_a4)
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

/-- What is proved of `$eo_prog_str-suffixof-one`. -/
def eo__24eo_5fprog_5fstr_2dsuffixof_2done.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dsuffixof_2done s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_suffixof_one x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-to-lower-concat`. -/
def eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_concat x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_prog_str-to-upper-concat`. -/
def eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_concat x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_prog_str-update-concat-fit0`. -/
def eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
    eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_concat_fit0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-update-fit`. -/
def eo__24eo_5fprog_5fstr_2dupdate_2dfit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fstr_2dupdate_2dfit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_fit x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-update-oob`. -/
def eo__24eo_5fprog_5fstr_2dupdate_2doob.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dupdate_2doob s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_oob x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_str-update-rev`. -/
def eo__24eo_5fprog_5fstr_2dupdate_2drev.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fstr_2dupdate_2drev s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_rev x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_string_code_inj`. -/
def eo__24eo_5fprog_5fstring_5fcode_5finj.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fstring_5fcode_5finj s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_code_inj x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_string_length_non_empty`. -/
def eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_length_non_empty x_a0)
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

/-- What is proved of `$eo_prog_uf-bv2nat-geq-elim`. -/
def eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_geq_elim x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_uf-bv2nat-int2bv`. -/
def eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_uf-bv2nat-int2bv-extend`. -/
def eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extend x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_uf-bv2nat-int2bv-extract`. -/
def eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extract x_a0 x_a1 x_a2 x_a3 x_a4)
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

/-- What is proved of `$eo_prog_uf-sbv-to-int-elim`. -/
def eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_sbv_to_int_elim x_a0 x_a1 x_a2 x_a3 x_a4)
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

/-- What is proved of `$eo_to_smt_bv_size`. -/
def eo__24eo_5fto_5fsmt_5fbv_5fsize.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fbv_5fsize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_bv_size x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_datatype`. -/
def eo__24eo_5fto_5fsmt_5fdatatype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fdatatype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_datatype_cons`. -/
def eo__24eo_5fto_5fsmt_5fdatatype_5fcons.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fdatatype_5fcons s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype_cons x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_datatype_decl`. -/
def eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype_decl x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_exists`. -/
def eo__24eo_5fto_5fsmt_5fexists.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fto_5fsmt_5fexists s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_exists x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_lambda_curry`. -/
def eo__24eo_5fto_5fsmt_5flambda_5fcurry.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fto_5fsmt_5flambda_5fcurry s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_lambda_curry x_a0 x_a1)
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

/-- What is proved of `$eo_to_smt_quantifiers_skolemize`. -/
def eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_quantifiers_skolemize x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_to_smt_tuple_select`. -/
def eo__24eo_5fto_5fsmt_5ftuple_5fselect.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5fto_5fsmt_5ftuple_5fselect s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tuple_select x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_type`. -/
def eo__24eo_5fto_5fsmt_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_type_tuple`. -/
def eo__24eo_5fto_5fsmt_5ftype_5ftuple.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fto_5fsmt_5ftype_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_type_tuple x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_updater_rec`. -/
def eo__24eo_5fto_5fsmt_5fupdater_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5fto_5fsmt_5fupdater_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_updater_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_+`. -/
def eo__24eo_5ftypeof_5f_2b.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_2b s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_plus x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_/`. -/
def eo__24eo_5ftypeof_5f_2f.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_2f s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_qdiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_<`. -/
def eo__24eo_5ftypeof_5f_3c.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_3c s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_lt x_a0 x_a1)
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

/-- What is proved of `$eo_typeof_@from_bools`. -/
def eo__24eo_5ftypeof_5f_40from_5fbools.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_40from_5fbools s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_from_bools x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@purify`. -/
def eo__24eo_5ftypeof_5f_40purify.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5f_40purify s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_purify x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_@quantifiers_skolemize`. -/
def eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_quantifiers_skolemize x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_typeof_abs`. -/
def eo__24eo_5ftypeof_5fabs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fabs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_abs x_a0)
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

/-- What is proved of `$eo_typeof_bvcomp`. -/
def eo__24eo_5ftypeof_5fbvcomp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fbvcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvcomp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_bvite`. -/
def eo__24eo_5ftypeof_5fbvite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fbvite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvite x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_typeof_bvredand`. -/
def eo__24eo_5ftypeof_5fbvredand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fbvredand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvredand x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_bvult`. -/
def eo__24eo_5ftypeof_5fbvult.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fbvult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvult x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_concat`. -/
def eo__24eo_5ftypeof_5fconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_concat x_a0 x_a1)
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

/-- What is proved of `$eo_typeof_extract`. -/
def eo__24eo_5ftypeof_5fextract.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5ftypeof_5fextract s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_extract x_a0 x_a1 x_a2 x_a3 x_a4)
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

/-- What is proved of `$eo_typeof_int_to_bv`. -/
def eo__24eo_5ftypeof_5fint_5fto_5fbv.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fint_5fto_5fbv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_int_to_bv x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_typeof_re.^`. -/
def eo__24eo_5ftypeof_5fre_2e_5e.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fre_2e_5e s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_re_exp x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_re.loop`. -/
def eo__24eo_5ftypeof_5fre_2eloop.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
    eo__24eo_5ftypeof_5fre_2eloop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_re_loop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_re.range`. -/
def eo__24eo_5ftypeof_5fre_2erange.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fre_2erange s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_re_range x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_repeat`. -/
def eo__24eo_5ftypeof_5frepeat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5frepeat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_repeat x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_rotate_left`. -/
def eo__24eo_5ftypeof_5frotate_5fleft.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5frotate_5fleft s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_rotate_left x_a0 x_a1 x_a2)
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

/-- What is proved of `$eo_typeof_tuple`. -/
def eo__24eo_5ftypeof_5ftuple.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_tuple x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_tuple.select`. -/
def eo__24eo_5ftypeof_5ftuple_2eselect.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5ftuple_2eselect s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_tuple_select x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_tuple.update`. -/
def eo__24eo_5ftypeof_5ftuple_2eupdate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24eo_5ftypeof_5ftuple_2eupdate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_tuple_update x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_update`. -/
def eo__24eo_5ftypeof_5fupdate.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fupdate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_update x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_zero_extend`. -/
def eo__24eo_5ftypeof_5fzero_5fextend.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24eo_5ftypeof_5fzero_5fextend s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_zero_extend x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$extract_antec`. -/
def eo__24extract_5fantec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24extract_5fantec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__extract_antec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$extract_antec_rec`. -/
def eo__24extract_5fantec_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24extract_5fantec_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__extract_antec_rec x_a0 x_a1)
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

/-- What is proved of `$get_nth_var_type`. -/
def eo__24get_5fnth_5fvar_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24get_5fnth_5fvar_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__get_nth_var_type x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$get_var_type`. -/
def eo__24get_5fvar_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24get_5fvar_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__get_var_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$greatest_int_lt`. -/
def eo__24greatest_5fint_5flt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24greatest_5fint_5flt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__greatest_int_lt x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$iota_rec`. -/
def eo__24iota_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24iota_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__iota_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$is_arith_type`. -/
def eo__24is_5farith_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24is_5farith_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_arith_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$is_poly_norm_rel_consts`. -/
def eo__24is_5fpoly_5fnorm_5frel_5fconsts.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24is_5fpoly_5fnorm_5frel_5fconsts s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_poly_norm_rel_consts x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$is_poly_norm_rel_consts_rel`. -/
def eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_poly_norm_rel_consts_rel x_a0)
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

/-- What is proved of `$least_int_gt`. -/
def eo__24least_5fint_5fgt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24least_5fint_5fgt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__least_int_gt x_a0)
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

/-- What is proved of `$mk_cong_rhs`. -/
def eo__24mk_5fcong_5frhs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_cong_rhs x_a0 x_a1)
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

/-- What is proved of `$mk_dt_inst_tuple`. -/
def eo__24mk_5fdt_5finst_5ftuple.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5fdt_5finst_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst_tuple x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_dt_inst_tuple_rec`. -/
def eo__24mk_5fdt_5finst_5ftuple_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fdt_5finst_5ftuple_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst_tuple_rec x_a0 x_a1 x_a2)
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

/-- What is proved of `$mk_nary_cong_rhs`. -/
def eo__24mk_5fnary_5fcong_5frhs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5fnary_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_nary_cong_rhs x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_quant_merge_prenex`. -/
def eo__24mk_5fquant_5fmerge_5fprenex.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fquant_5fmerge_5fprenex s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_quant_merge_prenex x_a0 x_a1 x_a2)
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

/-- What is proved of `$mk_re_unfold_neg_concat_fixed`. -/
def eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_unfold_neg_concat_fixed x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_re_unfold_pos`. -/
def eo__24mk_5fre_5funfold_5fpos.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24mk_5fre_5funfold_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_unfold_pos x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_re_unfold_pos_star`. -/
def eo__24mk_5fre_5funfold_5fpos_5fstar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fre_5funfold_5fpos_5fstar s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_unfold_pos_star x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$mk_skolems`. -/
def eo__24mk_5fskolems.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24mk_5fskolems s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_skolems x_a0 x_a1 x_a2)
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

/-- What is proved of `$poly_mod_coeffs`. -/
def eo__24poly_5fmod_5fcoeffs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24poly_5fmod_5fcoeffs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__poly_mod_coeffs x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$poly_neg`. -/
def eo__24poly_5fneg.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24poly_5fneg s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__poly_neg x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_concat_merge`. -/
def eo__24re_5fconcat_5fmerge.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_concat_merge x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_is_unbound_wildcard`. -/
def eo__24re_5fis_5funbound_5fwildcard.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24re_5fis_5funbound_5fwildcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_is_unbound_wildcard x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_nullable`. -/
def eo__24re_5fnullable.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_nullable x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_rev_comp`. -/
def eo__24re_5frev_5fcomp.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_rev_comp x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_rev_map_rev`. -/
def eo__24re_5frev_5fmap_5frev.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24re_5frev_5fmap_5frev s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_rev_map_rev x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_split_str_to_re`. -/
def eo__24re_5fsplit_5fstr_5fto_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24re_5fsplit_5fstr_5fto_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_split_str_to_re x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$re_unfold_pos_concat_rec`. -/
def eo__24re_5funfold_5fpos_5fconcat_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24re_5funfold_5fpos_5fconcat_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_unfold_pos_concat_rec x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$run_process_scope`. -/
def eo__24run_5fprocess_5fscope.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24run_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__run_process_scope x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$seq_element_of_unit`. -/
def eo__24seq_5felement_5fof_5funit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24seq_5felement_5fof_5funit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__seq_element_of_unit x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$seq_empty`. -/
def eo__24seq_5fempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24seq_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__seq_empty x_a0)
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

/-- What is proved of `$smtx_typeof_bv_op_2`. -/
def eo__24smtx_5ftypeof_5fbv_5fop_5f2.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fbv_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_bv_op_2_ret`. -/
def eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_concat`. -/
def eo__24smtx_5ftypeof_5fconcat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_dt_cons_rec`. -/
def eo__24smtx_5ftypeof_5fdt_5fcons_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$smtx_typeof_extract`. -/
def eo__24smtx_5ftypeof_5fextract.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fextract s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_extract x_a0 x_a1 x_a2)
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

/-- What is proved of `$smtx_typeof_sign_extend`. -/
def eo__24smtx_5ftypeof_5fsign_5fextend.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fsign_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_sign_extend x_a0 x_a1)
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

/-- What is proved of `$smtx_typeof_zero_extend`. -/
def eo__24smtx_5ftypeof_5fzero_5fextend.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24smtx_5ftypeof_5fzero_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_zero_extend x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_arith_entail_simple_rec`. -/
def eo__24str_5farith_5fentail_5fsimple_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24str_5farith_5fentail_5fsimple_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_arith_entail_simple_rec x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_fixed_len_re`. -/
def eo__24str_5ffixed_5flen_5fre.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_fixed_len_re x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_is_empty`. -/
def eo__24str_5fis_5fempty.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24str_5fis_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_empty x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_is_prefix_flat`. -/
def eo__24str_5fis_5fprefix_5fflat.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24str_5fis_5fprefix_5fflat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_prefix_flat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_leq_eval_rec`. -/
def eo__24str_5fleq_5feval_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24str_5fleq_5feval_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_leq_eval_rec x_a0 x_a1)
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

/-- What is proved of `$str_mk_ext_deq`. -/
def eo__24str_5fmk_5fext_5fdeq.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24str_5fmk_5fext_5fdeq s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_mk_ext_deq x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_mk_re_loop_elim_rec`. -/
def eo__24str_5fmk_5fre_5floop_5felim_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24str_5fmk_5fre_5floop_5felim_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_mk_re_loop_elim_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_mk_str_in_re_concat_star_char`. -/
def eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_mk_str_in_re_concat_star_char x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_mk_str_in_re_sigma_rec`. -/
def eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
    eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_mk_str_in_re_sigma_rec x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_mk_str_in_re_sigma_star_rec`. -/
def eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_mk_str_in_re_sigma_star_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_strip_prefix`. -/
def eo__24str_5fstrip_5fprefix.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24str_5fstrip_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_strip_prefix x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_to_int_eval_rec`. -/
def eo__24str_5fto_5fint_5feval_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24str_5fto_5fint_5feval_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_to_int_eval_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_unify_split`. -/
def eo__24str_5funify_5fsplit.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24str_5funify_5fsplit s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_unify_split x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$str_value_len`. -/
def eo__24str_5fvalue_5flen.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24str_5fvalue_5flen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_value_len x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$strip_even_exponent`. -/
def eo__24strip_5feven_5fexponent.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24strip_5feven_5fexponent s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__strip_even_exponent x_a0 x_a1)
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

/-- What is proved of `$tuple_collapse_updater_rhs`. -/
def eo__24tuple_5fcollapse_5fupdater_5frhs.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24tuple_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__tuple_collapse_updater_rhs x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$tuple_get_selectors_rec`. -/
def eo__24tuple_5fget_5fselectors_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24tuple_5fget_5fselectors_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__tuple_get_selectors_rec x_a0 x_a1)
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
  eo__24abconv_5fint_5fto_5fbv_5felim : eo__24abconv_5fint_5fto_5fbv_5felim.Spec n
  eo__24abconv_5fubv_5fto_5fint_5felim : eo__24abconv_5fubv_5fto_5fint_5felim.Spec n
  eo__24arith_5fmk_5fone : eo__24arith_5fmk_5fone.Spec n
  eo__24arith_5fmk_5fzero : eo__24arith_5fmk_5fzero.Spec n
  eo__24arith_5fnormalize_5flit : eo__24arith_5fnormalize_5flit.Spec n
  eo__24arith_5frel_5finv : eo__24arith_5frel_5finv.Spec n
  eo__24arith_5frel_5fneg : eo__24arith_5frel_5fneg.Spec n
  eo__24arith_5frel_5fsum : eo__24arith_5frel_5fsum.Spec n
  eo__24arith_5frel_5ftrichotomy : eo__24arith_5frel_5ftrichotomy.Spec n
  eo__24assoc_5fnil_5fnth : eo__24assoc_5fnil_5fnth.Spec n
  eo__24bv_5fbitblast_5fapply_5fbinary : eo__24bv_5fbitblast_5fapply_5fbinary.Spec n
  eo__24bv_5fbitblast_5fapply_5fite : eo__24bv_5fbitblast_5fapply_5fite.Spec n
  eo__24bv_5fbitblast_5fapply_5funary : eo__24bv_5fbitblast_5fapply_5funary.Spec n
  eo__24bv_5fbitblast_5fbinary_5fapp : eo__24bv_5fbitblast_5fbinary_5fapp.Spec n
  eo__24bv_5fbitblast_5fconcat : eo__24bv_5fbitblast_5fconcat.Spec n
  eo__24bv_5fbitblast_5fhead : eo__24bv_5fbitblast_5fhead.Spec n
  eo__24bv_5fbitblast_5fprefix : eo__24bv_5fbitblast_5fprefix.Spec n
  eo__24bv_5fbitblast_5fslt_5fimpl : eo__24bv_5fbitblast_5fslt_5fimpl.Spec n
  eo__24bv_5fbitblast_5fsubsequence : eo__24bv_5fbitblast_5fsubsequence.Spec n
  eo__24bv_5fbitblast_5ftail : eo__24bv_5fbitblast_5ftail.Spec n
  eo__24bv_5fbitblast_5fult : eo__24bv_5fbitblast_5fult.Spec n
  eo__24bv_5fbitblast_5fult_5frec : eo__24bv_5fbitblast_5fult_5frec.Spec n
  eo__24bv_5fbitwidth : eo__24bv_5fbitwidth.Spec n
  eo__24bv_5fget_5ffirst_5fconst_5fchild : eo__24bv_5fget_5ffirst_5fconst_5fchild.Spec n
  eo__24bv_5fmk_5fbitblast_5fstep_5fadd : eo__24bv_5fmk_5fbitblast_5fstep_5fadd.Spec n
  eo__24bv_5fmk_5fbitblast_5fstep_5fconcat : eo__24bv_5fmk_5fbitblast_5fstep_5fconcat.Spec n
  eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec : eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec.Spec n
  eo__24bv_5fmk_5fbitblast_5fstep_5fite : eo__24bv_5fmk_5fbitblast_5fstep_5fite.Spec n
  eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec : eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.Spec n
  eo__24bv_5fripple_5fcarry_5fadder_5f2 : eo__24bv_5fripple_5fcarry_5fadder_5f2.Spec n
  eo__24chain_5fm_5fresolve : eo__24chain_5fm_5fresolve.Spec n
  eo__24chain_5fm_5fresolve_5ffinal : eo__24chain_5fm_5fresolve_5ffinal.Spec n
  eo__24chain_5fm_5fresolve_5frec : eo__24chain_5fm_5fresolve_5frec.Spec n
  eo__24chain_5fm_5fresolve_5frec_5fstep : eo__24chain_5fm_5fresolve_5frec_5fstep.Spec n
  eo__24compute_5fcard : eo__24compute_5fcard.Spec n
  eo__24dt_5farg_5flist : eo__24dt_5farg_5flist.Spec n
  eo__24dt_5fcollapse_5fupdater_5frhs : eo__24dt_5fcollapse_5fupdater_5frhs.Spec n
  eo__24eo_5fStateObj_5fproven : eo__24eo_5fStateObj_5fproven.Spec n
  eo__24eo_5fcmd_5fstep_5fpop_5fproven : eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec n
  eo__24eo_5fdd_5flookup : eo__24eo_5fdd_5flookup.Spec n
  eo__24eo_5fdd_5fresolve : eo__24eo_5fdd_5fresolve.Spec n
  eo__24eo_5fdisamb_5ftype_5fseq_2eempty : eo__24eo_5fdisamb_5ftype_5fseq_2eempty.Spec n
  eo__24eo_5fdisamb_5ftype_5fset_2eempty : eo__24eo_5fdisamb_5ftype_5fset_2eempty.Spec n
  eo__24eo_5fdt_5fresolve : eo__24eo_5fdt_5fresolve.Spec n
  eo__24eo_5fdtc_5fresolve : eo__24eo_5fdtc_5fresolve.Spec n
  eo__24eo_5finvoke_5fcmd_5fcheck_5fproven : eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec n
  eo__24eo_5fis_5flist_5fnil : eo__24eo_5fis_5flist_5fnil.Spec n
  eo__24eo_5fis_5flist_5fnil_5f_2a : eo__24eo_5fis_5flist_5fnil_5f_2a.Spec n
  eo__24eo_5fis_5flist_5fnil_5f_2b : eo__24eo_5fis_5flist_5fnil_5f_2b.Spec n
  eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs : eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.Spec n
  eo__24eo_5fis_5flist_5fnil_5fbvadd : eo__24eo_5fis_5flist_5fnil_5fbvadd.Spec n
  eo__24eo_5fis_5flist_5fnil_5fbvand : eo__24eo_5fis_5flist_5fnil_5fbvand.Spec n
  eo__24eo_5fis_5flist_5fnil_5fbvmul : eo__24eo_5fis_5flist_5fnil_5fbvmul.Spec n
  eo__24eo_5fis_5flist_5fnil_5fbvor : eo__24eo_5fis_5flist_5fnil_5fbvor.Spec n
  eo__24eo_5fis_5flist_5fnil_5fbvxor : eo__24eo_5fis_5flist_5fnil_5fbvxor.Spec n
  eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b : eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b.Spec n
  eo__24eo_5flit_5ftype_5fBinary : eo__24eo_5flit_5ftype_5fBinary.Spec n
  eo__24eo_5flit_5ftype_5fNumeral : eo__24eo_5flit_5ftype_5fNumeral.Spec n
  eo__24eo_5flit_5ftype_5fRational : eo__24eo_5flit_5ftype_5fRational.Spec n
  eo__24eo_5flit_5ftype_5fString : eo__24eo_5flit_5ftype_5fString.Spec n
  eo__24eo_5fnil : eo__24eo_5fnil.Spec n
  eo__24eo_5fnil_5f_2a : eo__24eo_5fnil_5f_2a.Spec n
  eo__24eo_5fnil_5f_2b : eo__24eo_5fnil_5f_2b.Spec n
  eo__24eo_5fnil_5f_40_40TypedList_2econs : eo__24eo_5fnil_5f_40_40TypedList_2econs.Spec n
  eo__24eo_5fnil_5fbvadd : eo__24eo_5fnil_5fbvadd.Spec n
  eo__24eo_5fnil_5fbvand : eo__24eo_5fnil_5fbvand.Spec n
  eo__24eo_5fnil_5fbvmul : eo__24eo_5fnil_5fbvmul.Spec n
  eo__24eo_5fnil_5fbvor : eo__24eo_5fnil_5fbvor.Spec n
  eo__24eo_5fnil_5fbvxor : eo__24eo_5fnil_5fbvxor.Spec n
  eo__24eo_5fnil_5fstr_2e_2b_2b : eo__24eo_5fnil_5fstr_2e_2b_2b.Spec n
  eo__24eo_5fprog_5fand_5felim : eo__24eo_5fprog_5fand_5felim.Spec n
  eo__24eo_5fprog_5fand_5fintro : eo__24eo_5fprog_5fand_5fintro.Spec n
  eo__24eo_5fprog_5farith_2dabs_2deq : eo__24eo_5fprog_5farith_2dabs_2deq.Spec n
  eo__24eo_5fprog_5farith_2dabs_2dint_2dgt : eo__24eo_5fprog_5farith_2dabs_2dint_2dgt.Spec n
  eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt : eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt.Spec n
  eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal : eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal.Spec n
  eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal : eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal.Spec n
  eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint : eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint.Spec n
  eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal : eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal.Spec n
  eo__24eo_5fprog_5farith_2ddivisible_2delim : eo__24eo_5fprog_5farith_2ddivisible_2delim.Spec n
  eo__24eo_5fprog_5farith_2delim_2dgt : eo__24eo_5fprog_5farith_2delim_2dgt.Spec n
  eo__24eo_5fprog_5farith_2delim_2dint_2dgt : eo__24eo_5fprog_5farith_2delim_2dint_2dgt.Spec n
  eo__24eo_5fprog_5farith_2delim_2dint_2dlt : eo__24eo_5fprog_5farith_2delim_2dint_2dlt.Spec n
  eo__24eo_5fprog_5farith_2delim_2dleq : eo__24eo_5fprog_5farith_2delim_2dleq.Spec n
  eo__24eo_5fprog_5farith_2delim_2dlt : eo__24eo_5fprog_5farith_2delim_2dlt.Spec n
  eo__24eo_5fprog_5farith_2deq_2delim_2dint : eo__24eo_5fprog_5farith_2deq_2delim_2dint.Spec n
  eo__24eo_5fprog_5farith_2deq_2delim_2dreal : eo__24eo_5fprog_5farith_2deq_2delim_2dreal.Spec n
  eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift : eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift.Spec n
  eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint : eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint.Spec n
  eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal : eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal.Spec n
  eo__24eo_5fprog_5farith_2dgeq_2dtighten : eo__24eo_5fprog_5farith_2dgeq_2dtighten.Spec n
  eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal : eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal.Spec n
  eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg : eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg.Spec n
  eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done : eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done.Spec n
  eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod : eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod.Spec n
  eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero : eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero.Spec n
  eo__24eo_5fprog_5farith_2dint_2deq_2dconflict : eo__24eo_5fprog_5farith_2dint_2deq_2dconflict.Spec n
  eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal : eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal.Spec n
  eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg : eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg.Spec n
  eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done : eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done.Spec n
  eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero : eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero.Spec n
  eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal : eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal.Spec n
  eo__24eo_5fprog_5farith_2dleq_2dite_2dlift : eo__24eo_5fprog_5farith_2dleq_2dite_2dlift.Spec n
  eo__24eo_5fprog_5farith_2dleq_2dnorm : eo__24eo_5fprog_5farith_2dleq_2dnorm.Spec n
  eo__24eo_5fprog_5farith_2dmax_2dgeq1 : eo__24eo_5fprog_5farith_2dmax_2dgeq1.Spec n
  eo__24eo_5fprog_5farith_2dmax_2dgeq2 : eo__24eo_5fprog_5farith_2dmax_2dgeq2.Spec n
  eo__24eo_5fprog_5farith_2dmin_2dlt1 : eo__24eo_5fprog_5farith_2dmin_2dlt1.Spec n
  eo__24eo_5fprog_5farith_2dmin_2dlt2 : eo__24eo_5fprog_5farith_2dmin_2dlt2.Spec n
  eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1 : eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1.Spec n
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
  eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra : eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra.Spec n
  eo__24eo_5fprog_5fbool_2dand_2dconf : eo__24eo_5fprog_5fbool_2dand_2dconf.Spec n
  eo__24eo_5fprog_5fbool_2dand_2dconf2 : eo__24eo_5fprog_5fbool_2dand_2dconf2.Spec n
  eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan : eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan.Spec n
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
  eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib : eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1 : eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2 : eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dfalse : eo__24eo_5fprog_5fbool_2dnot_2dfalse.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dite_2delim : eo__24eo_5fprog_5fbool_2dnot_2dite_2delim.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dtrue : eo__24eo_5fprog_5fbool_2dnot_2dtrue.Spec n
  eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim : eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim.Spec n
  eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib : eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib.Spec n
  eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan : eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan.Spec n
  eo__24eo_5fprog_5fbool_2dor_2dtaut : eo__24eo_5fprog_5fbool_2dor_2dtaut.Spec n
  eo__24eo_5fprog_5fbool_2dor_2dtaut2 : eo__24eo_5fprog_5fbool_2dor_2dtaut2.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dcomm : eo__24eo_5fprog_5fbool_2dxor_2dcomm.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2delim : eo__24eo_5fprog_5fbool_2dxor_2delim.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dfalse : eo__24eo_5fprog_5fbool_2dxor_2dfalse.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dnrefl : eo__24eo_5fprog_5fbool_2dxor_2dnrefl.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2drefl : eo__24eo_5fprog_5fbool_2dxor_2drefl.Spec n
  eo__24eo_5fprog_5fbool_2dxor_2dtrue : eo__24eo_5fprog_5fbool_2dxor_2dtrue.Spec n
  eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0 : eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0.Spec n
  eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1 : eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2 : eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dashr_2dzero : eo__24eo_5fprog_5fbv_2dashr_2dzero.Spec n
  eo__24eo_5fprog_5fbv_2dcommutative_2dcomp : eo__24eo_5fprog_5fbv_2dcommutative_2dcomp.Spec n
  eo__24eo_5fprog_5fbv_2dcomp_2deliminate : eo__24eo_5fprog_5fbv_2dcomp_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2 : eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2.Spec n
  eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3 : eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3.Spec n
  eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve : eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1 : eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dextract : eo__24eo_5fprog_5fbv_2dextract_2dextract.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dnot : eo__24eo_5fprog_5fbv_2dextract_2dnot.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1 : eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3 : eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3.Spec n
  eo__24eo_5fprog_5fbv_2dextract_2dwhole : eo__24eo_5fprog_5fbv_2dextract_2dwhole.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1 : eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2 : eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1 : eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2 : eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren : eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2 : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3 : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse : eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif : eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse : eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif : eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dwidth_2done : eo__24eo_5fprog_5fbv_2dite_2dwidth_2done.Spec n
  eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot : eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot.Spec n
  eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0 : eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0.Spec n
  eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 : eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 : eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dlshr_2dzero : eo__24eo_5fprog_5fbv_2dlshr_2dzero.Spec n
  eo__24eo_5fprog_5fbv_2dlt_2dself : eo__24eo_5fprog_5fbv_2dlt_2dself.Spec n
  eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1 : eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 : eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dnego_2deliminate : eo__24eo_5fprog_5fbv_2dnego_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dnot_2didemp : eo__24eo_5fprog_5fbv_2dnot_2didemp.Spec n
  eo__24eo_5fprog_5fbv_2dnot_2dneq : eo__24eo_5fprog_5fbv_2dnot_2dneq.Spec n
  eo__24eo_5fprog_5fbv_2dnot_2dult : eo__24eo_5fprog_5fbv_2dnot_2dult.Spec n
  eo__24eo_5fprog_5fbv_2dnot_2dxor : eo__24eo_5fprog_5fbv_2dnot_2dxor.Spec n
  eo__24eo_5fprog_5fbv_2dredand_2deliminate : eo__24eo_5fprog_5fbv_2dredand_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dredor_2deliminate : eo__24eo_5fprog_5fbv_2dredor_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2 : eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2.Spec n
  eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2 : eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dsdivo_2deliminate : eo__24eo_5fprog_5fbv_2dsdivo_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dsge_2deliminate : eo__24eo_5fprog_5fbv_2dsge_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dsgt_2deliminate : eo__24eo_5fprog_5fbv_2dsgt_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0 : eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0.Spec n
  eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 : eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 : eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dshl_2dzero : eo__24eo_5fprog_5fbv_2dshl_2dzero.Spec n
  eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0 : eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0.Spec n
  eo__24eo_5fprog_5fbv_2dsle_2deliminate : eo__24eo_5fprog_5fbv_2dsle_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dsle_2dself : eo__24eo_5fprog_5fbv_2dsle_2dself.Spec n
  eo__24eo_5fprog_5fbv_2dsrem_2deliminate : eo__24eo_5fprog_5fbv_2dsrem_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dudiv_2done : eo__24eo_5fprog_5fbv_2dudiv_2done.Spec n
  eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done : eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.Spec n
  eo__24eo_5fprog_5fbv_2dudiv_2dzero : eo__24eo_5fprog_5fbv_2dudiv_2dzero.Spec n
  eo__24eo_5fprog_5fbv_2duge_2deliminate : eo__24eo_5fprog_5fbv_2duge_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dugt_2deliminate : eo__24eo_5fprog_5fbv_2dugt_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dugt_2durem : eo__24eo_5fprog_5fbv_2dugt_2durem.Spec n
  eo__24eo_5fprog_5fbv_2dule_2deliminate : eo__24eo_5fprog_5fbv_2dule_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dule_2dmax : eo__24eo_5fprog_5fbv_2dule_2dmax.Spec n
  eo__24eo_5fprog_5fbv_2dule_2dself : eo__24eo_5fprog_5fbv_2dule_2dself.Spec n
  eo__24eo_5fprog_5fbv_2dule_2dzero : eo__24eo_5fprog_5fbv_2dule_2dzero.Spec n
  eo__24eo_5fprog_5fbv_2dult_2done : eo__24eo_5fprog_5fbv_2dult_2done.Spec n
  eo__24eo_5fprog_5fbv_2dult_2dself : eo__24eo_5fprog_5fbv_2dult_2dself.Spec n
  eo__24eo_5fprog_5fbv_2dult_2dzero_2d1 : eo__24eo_5fprog_5fbv_2dult_2dzero_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dult_2dzero_2d2 : eo__24eo_5fprog_5fbv_2dult_2dzero_2d2.Spec n
  eo__24eo_5fprog_5fbv_2durem_2done : eo__24eo_5fprog_5fbv_2durem_2done.Spec n
  eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done : eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done.Spec n
  eo__24eo_5fprog_5fbv_2durem_2dself : eo__24eo_5fprog_5fbv_2durem_2dself.Spec n
  eo__24eo_5fprog_5fbv_2dusubo_2deliminate : eo__24eo_5fprog_5fbv_2dusubo_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate : eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate.Spec n
  eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0 : eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0.Spec n
  eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1 : eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1.Spec n
  eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2 : eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2.Spec n
  eo__24eo_5fprog_5fbv_2dzero_2dule : eo__24eo_5fprog_5fbv_2dzero_2dule.Spec n
  eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq : eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq.Spec n
  eo__24eo_5fprog_5fchain_5fm_5fresolution : eo__24eo_5fprog_5fchain_5fm_5fresolution.Spec n
  eo__24eo_5fprog_5fchain_5fresolution : eo__24eo_5fprog_5fchain_5fresolution.Spec n
  eo__24eo_5fprog_5fcnf_5fand_5fneg : eo__24eo_5fprog_5fcnf_5fand_5fneg.Spec n
  eo__24eo_5fprog_5fcnf_5fand_5fpos : eo__24eo_5fprog_5fcnf_5fand_5fpos.Spec n
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
  eo__24eo_5fprog_5fcnf_5for_5fneg : eo__24eo_5fprog_5fcnf_5for_5fneg.Spec n
  eo__24eo_5fprog_5fcnf_5for_5fpos : eo__24eo_5fprog_5fcnf_5for_5fpos.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fneg1 : eo__24eo_5fprog_5fcnf_5fxor_5fneg1.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fneg2 : eo__24eo_5fprog_5fcnf_5fxor_5fneg2.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fpos1 : eo__24eo_5fprog_5fcnf_5fxor_5fpos1.Spec n
  eo__24eo_5fprog_5fcnf_5fxor_5fpos2 : eo__24eo_5fprog_5fcnf_5fxor_5fpos2.Spec n
  eo__24eo_5fprog_5fcong : eo__24eo_5fprog_5fcong.Spec n
  eo__24eo_5fprog_5fcontra : eo__24eo_5fprog_5fcontra.Spec n
  eo__24eo_5fprog_5fdistinct_2delim : eo__24eo_5fprog_5fdistinct_2delim.Spec n
  eo__24eo_5fprog_5fdistinct_2dfalse : eo__24eo_5fprog_5fdistinct_2dfalse.Spec n
  eo__24eo_5fprog_5feq_2dcond_2ddeq : eo__24eo_5fprog_5feq_2dcond_2ddeq.Spec n
  eo__24eo_5fprog_5feq_2dite_2dlift : eo__24eo_5fprog_5feq_2dite_2dlift.Spec n
  eo__24eo_5fprog_5feq_2drefl : eo__24eo_5fprog_5feq_2drefl.Spec n
  eo__24eo_5fprog_5feq_2dsymm : eo__24eo_5fprog_5feq_2dsymm.Spec n
  eo__24eo_5fprog_5feq_5fresolve : eo__24eo_5fprog_5feq_5fresolve.Spec n
  eo__24eo_5fprog_5fequiv_5felim1 : eo__24eo_5fprog_5fequiv_5felim1.Spec n
  eo__24eo_5fprog_5fequiv_5felim2 : eo__24eo_5fprog_5fequiv_5felim2.Spec n
  eo__24eo_5fprog_5fexists_2delim : eo__24eo_5fprog_5fexists_2delim.Spec n
  eo__24eo_5fprog_5fexists_5fstring_5flength : eo__24eo_5fprog_5fexists_5fstring_5flength.Spec n
  eo__24eo_5fprog_5ffactoring : eo__24eo_5fprog_5ffactoring.Spec n
  eo__24eo_5fprog_5ffalse_5felim : eo__24eo_5fprog_5ffalse_5felim.Spec n
  eo__24eo_5fprog_5ffalse_5fintro : eo__24eo_5fprog_5ffalse_5fintro.Spec n
  eo__24eo_5fprog_5fho_5fcong : eo__24eo_5fprog_5fho_5fcong.Spec n
  eo__24eo_5fprog_5fimplies_5felim : eo__24eo_5fprog_5fimplies_5felim.Spec n
  eo__24eo_5fprog_5fint_5ftight_5flb : eo__24eo_5fprog_5fint_5ftight_5flb.Spec n
  eo__24eo_5fprog_5fint_5ftight_5fub : eo__24eo_5fprog_5fint_5ftight_5fub.Spec n
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
  eo__24eo_5fprog_5fnary_5fcong : eo__24eo_5fprog_5fnary_5fcong.Spec n
  eo__24eo_5fprog_5fnot_5fand : eo__24eo_5fprog_5fnot_5fand.Spec n
  eo__24eo_5fprog_5fnot_5fequiv_5felim1 : eo__24eo_5fprog_5fnot_5fequiv_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fequiv_5felim2 : eo__24eo_5fprog_5fnot_5fequiv_5felim2.Spec n
  eo__24eo_5fprog_5fnot_5fimplies_5felim1 : eo__24eo_5fprog_5fnot_5fimplies_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fimplies_5felim2 : eo__24eo_5fprog_5fnot_5fimplies_5felim2.Spec n
  eo__24eo_5fprog_5fnot_5fite_5felim1 : eo__24eo_5fprog_5fnot_5fite_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fite_5felim2 : eo__24eo_5fprog_5fnot_5fite_5felim2.Spec n
  eo__24eo_5fprog_5fnot_5fnot_5felim : eo__24eo_5fprog_5fnot_5fnot_5felim.Spec n
  eo__24eo_5fprog_5fnot_5for_5felim : eo__24eo_5fprog_5fnot_5for_5felim.Spec n
  eo__24eo_5fprog_5fnot_5fxor_5felim1 : eo__24eo_5fprog_5fnot_5fxor_5felim1.Spec n
  eo__24eo_5fprog_5fnot_5fxor_5felim2 : eo__24eo_5fprog_5fnot_5fxor_5felim2.Spec n
  eo__24eo_5fprog_5fpairwise_5fcong : eo__24eo_5fprog_5fpairwise_5fcong.Spec n
  eo__24eo_5fprog_5fprocess_5fscope : eo__24eo_5fprog_5fprocess_5fscope.Spec n
  eo__24eo_5fprog_5fquant_2dmerge_2dprenex : eo__24eo_5fprog_5fquant_2dmerge_2dprenex.Spec n
  eo__24eo_5fprog_5fquant_2dminiscope_2dand : eo__24eo_5fprog_5fquant_2dminiscope_2dand.Spec n
  eo__24eo_5fprog_5fre_2dconcat_2dmerge : eo__24eo_5fprog_5fre_2dconcat_2dmerge.Spec n
  eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat : eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat.Spec n
  eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap : eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap.Spec n
  eo__24eo_5fprog_5fre_2ddiff_2delim : eo__24eo_5fprog_5fre_2ddiff_2delim.Spec n
  eo__24eo_5fprog_5fre_2din_2dcomp : eo__24eo_5fprog_5fre_2din_2dcomp.Spec n
  eo__24eo_5fprog_5fre_2din_2dcstring : eo__24eo_5fprog_5fre_2din_2dcstring.Spec n
  eo__24eo_5fprog_5fre_2din_2dempty : eo__24eo_5fprog_5fre_2din_2dempty.Spec n
  eo__24eo_5fprog_5fre_2din_2dsigma : eo__24eo_5fprog_5fre_2din_2dsigma.Spec n
  eo__24eo_5fprog_5fre_2din_2dsigma_2dstar : eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.Spec n
  eo__24eo_5fprog_5fre_2dinter_2dall : eo__24eo_5fprog_5fre_2dinter_2dall.Spec n
  eo__24eo_5fprog_5fre_2dinter_2dcstring : eo__24eo_5fprog_5fre_2dinter_2dcstring.Spec n
  eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg : eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg.Spec n
  eo__24eo_5fprog_5fre_2dloop_2dneg : eo__24eo_5fprog_5fre_2dloop_2dneg.Spec n
  eo__24eo_5fprog_5fre_2dloop_2dstar : eo__24eo_5fprog_5fre_2dloop_2dstar.Spec n
  eo__24eo_5fprog_5fre_2dopt_2delim : eo__24eo_5fprog_5fre_2dopt_2delim.Spec n
  eo__24eo_5fprog_5fre_2dplus_2delim : eo__24eo_5fprog_5fre_2dplus_2delim.Spec n
  eo__24eo_5fprog_5fre_2drange_2demp : eo__24eo_5fprog_5fre_2drange_2demp.Spec n
  eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1 : eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1.Spec n
  eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2 : eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2.Spec n
  eo__24eo_5fprog_5fre_2drange_2drefl : eo__24eo_5fprog_5fre_2drange_2drefl.Spec n
  eo__24eo_5fprog_5fre_2drepeat_2delim : eo__24eo_5fprog_5fre_2drepeat_2delim.Spec n
  eo__24eo_5fprog_5fre_2dstar_2dstar : eo__24eo_5fprog_5fre_2dstar_2dstar.Spec n
  eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar : eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar.Spec n
  eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp : eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp.Spec n
  eo__24eo_5fprog_5fre_2dunion_2dall : eo__24eo_5fprog_5fre_2dunion_2dall.Spec n
  eo__24eo_5fprog_5fre_2dunion_2dconst_2delim : eo__24eo_5fprog_5fre_2dunion_2dconst_2delim.Spec n
  eo__24eo_5fprog_5fre_5fconcat : eo__24eo_5fprog_5fre_5fconcat.Spec n
  eo__24eo_5fprog_5fre_5finter : eo__24eo_5fprog_5fre_5finter.Spec n
  eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed : eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed.Spec n
  eo__24eo_5fprog_5fre_5funfold_5fpos : eo__24eo_5fprog_5fre_5funfold_5fpos.Spec n
  eo__24eo_5fprog_5frefl : eo__24eo_5fprog_5frefl.Spec n
  eo__24eo_5fprog_5freordering : eo__24eo_5fprog_5freordering.Spec n
  eo__24eo_5fprog_5fresolution : eo__24eo_5fprog_5fresolution.Spec n
  eo__24eo_5fprog_5fscope : eo__24eo_5fprog_5fscope.Spec n
  eo__24eo_5fprog_5fseq_2dlen_2drev : eo__24eo_5fprog_5fseq_2dlen_2drev.Spec n
  eo__24eo_5fprog_5fseq_2dlen_2dunit : eo__24eo_5fprog_5fseq_2dlen_2dunit.Spec n
  eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit : eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit.Spec n
  eo__24eo_5fprog_5fseq_2dnth_2dunit : eo__24eo_5fprog_5fseq_2dnth_2dunit.Spec n
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
  eo__24eo_5fprog_5fstr_2dat_2delim : eo__24eo_5fprog_5fstr_2dat_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dconcat_2dclash : eo__24eo_5fprog_5fstr_2dconcat_2dclash.Spec n
  eo__24eo_5fprog_5fstr_2dconcat_2dclash2 : eo__24eo_5fprog_5fstr_2dconcat_2dclash2.Spec n
  eo__24eo_5fprog_5fstr_2dconcat_2dunify : eo__24eo_5fprog_5fstr_2dconcat_2dunify.Spec n
  eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase : eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2dchar : eo__24eo_5fprog_5fstr_2dcontains_2dchar.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2demp : eo__24eo_5fprog_5fstr_2dcontains_2demp.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq : eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drefl : eo__24eo_5fprog_5fstr_2dcontains_2drefl.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt.Spec n
  eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar : eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar.Spec n
  eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1 : eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1.Spec n
  eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2 : eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2.Spec n
  eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse : eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp : eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix : eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp : eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange : eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp : eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc : eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc.Spec n
  eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen : eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit : eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit.Spec n
  eo__24eo_5fprog_5fstr_2din_2dre_2dcontains : eo__24eo_5fprog_5fstr_2din_2dre_2dcontains.Spec n
  eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange : eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange.Spec n
  eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange : eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange.Spec n
  eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim : eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim.Spec n
  eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim : eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim.Spec n
  eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim : eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dcontains_2dpre : eo__24eo_5fprog_5fstr_2dindexof_2dcontains_2dpre.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dfind_2demp : eo__24eo_5fprog_5fstr_2dindexof_2dfind_2demp.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob : eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob2 : eo__24eo_5fprog_5fstr_2dindexof_2dlen_2doob2.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dno_2dcontains : eo__24eo_5fprog_5fstr_2dindexof_2dno_2dcontains.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2doob : eo__24eo_5fprog_5fstr_2dindexof_2doob.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2doob2 : eo__24eo_5fprog_5fstr_2dindexof_2doob2.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dre_2demp_2dre : eo__24eo_5fprog_5fstr_2dindexof_2dre_2demp_2dre.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dre_2dnone : eo__24eo_5fprog_5fstr_2dindexof_2dre_2dnone.Spec n
  eo__24eo_5fprog_5fstr_2dindexof_2dself : eo__24eo_5fprog_5fstr_2dindexof_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dis_2ddigit_2delim : eo__24eo_5fprog_5fstr_2dis_2ddigit_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dconcat_2drec : eo__24eo_5fprog_5fstr_2dlen_2dconcat_2drec.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dbase : eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dbase.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dconcat_2drec : eo__24eo_5fprog_5fstr_2dlen_2deq_2dzero_2dconcat_2drec.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv : eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv : eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange : eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange.Spec n
  eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv : eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv.Spec n
  eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d1 : eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d1.Spec n
  eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d2 : eo__24eo_5fprog_5fstr_2dleq_2dconcat_2dbase_2d2.Spec n
  eo__24eo_5fprog_5fstr_2dleq_2dempty : eo__24eo_5fprog_5fstr_2dleq_2dempty.Spec n
  eo__24eo_5fprog_5fstr_2dleq_2dempty_2deq : eo__24eo_5fprog_5fstr_2dleq_2dempty_2deq.Spec n
  eo__24eo_5fprog_5fstr_2dlt_2delim : eo__24eo_5fprog_5fstr_2dlt_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dprefixof_2delim : eo__24eo_5fprog_5fstr_2dprefixof_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dprefixof_2deq : eo__24eo_5fprog_5fstr_2dprefixof_2deq.Spec n
  eo__24eo_5fprog_5fstr_2dprefixof_2done : eo__24eo_5fprog_5fstr_2dprefixof_2done.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite1.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite2 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dite2.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dself : eo__24eo_5fprog_5fstr_2drepl_2drepl_2ddual_2dself.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlen_2did : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlen_2did.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3 : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dall_2did : eo__24eo_5fprog_5fstr_2dreplace_2dall_2did.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn : eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse : eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc : eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2did : eo__24eo_5fprog_5fstr_2dreplace_2did.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains : eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dprefix : eo__24eo_5fprog_5fstr_2dreplace_2dprefix.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone : eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone : eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dself : eo__24eo_5fprog_5fstr_2dreplace_2dself.Spec n
  eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp : eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen : eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1 : eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2 : eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1 : eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dconcat2 : eo__24eo_5fprog_5fstr_2dsubstr_2dconcat2.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dctn : eo__24eo_5fprog_5fstr_2dsubstr_2dctn.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dctn_2dcontra : eo__24eo_5fprog_5fstr_2dsubstr_2dctn_2dcontra.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange : eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart : eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg : eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr : eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty : eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen : eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dfull : eo__24eo_5fprog_5fstr_2dsubstr_2dfull.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dfull_2deq : eo__24eo_5fprog_5fstr_2dsubstr_2dfull_2deq.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude : eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm : eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dreplace : eo__24eo_5fprog_5fstr_2dsubstr_2dreplace.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen : eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq : eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq.Spec n
  eo__24eo_5fprog_5fstr_2dsuffixof_2delim : eo__24eo_5fprog_5fstr_2dsuffixof_2delim.Spec n
  eo__24eo_5fprog_5fstr_2dsuffixof_2deq : eo__24eo_5fprog_5fstr_2dsuffixof_2deq.Spec n
  eo__24eo_5fprog_5fstr_2dsuffixof_2done : eo__24eo_5fprog_5fstr_2dsuffixof_2done.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat : eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint : eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2didem : eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen : eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper : eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat : eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint : eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2didem : eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.Spec n
  eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.Spec n
  eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 : eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.Spec n
  eo__24eo_5fprog_5fstr_2dupdate_2dfit : eo__24eo_5fprog_5fstr_2dupdate_2dfit.Spec n
  eo__24eo_5fprog_5fstr_2dupdate_2doob : eo__24eo_5fprog_5fstr_2dupdate_2doob.Spec n
  eo__24eo_5fprog_5fstr_2dupdate_2drev : eo__24eo_5fprog_5fstr_2dupdate_2drev.Spec n
  eo__24eo_5fprog_5fstring_5fcode_5finj : eo__24eo_5fprog_5fstring_5fcode_5finj.Spec n
  eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty : eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.Spec n
  eo__24eo_5fprog_5fstring_5fseq_5funit_5finj : eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.Spec n
  eo__24eo_5fprog_5fsymm : eo__24eo_5fprog_5fsymm.Spec n
  eo__24eo_5fprog_5ftrans : eo__24eo_5fprog_5ftrans.Spec n
  eo__24eo_5fprog_5ftrue_5felim : eo__24eo_5fprog_5ftrue_5felim.Spec n
  eo__24eo_5fprog_5ftrue_5fintro : eo__24eo_5fprog_5ftrue_5fintro.Spec n
  eo__24eo_5fprog_5ftrust : eo__24eo_5fprog_5ftrust.Spec n
  eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim : eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.Spec n
  eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.Spec n
  eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.Spec n
  eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.Spec n
  eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat : eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.Spec n
  eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv : eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.Spec n
  eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv : eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.Spec n
  eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim : eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.Spec n
  eo__24eo_5fprog_5fxor_5felim1 : eo__24eo_5fprog_5fxor_5felim1.Spec n
  eo__24eo_5fprog_5fxor_5felim2 : eo__24eo_5fprog_5fxor_5felim2.Spec n
  eo__24eo_5fpush_5fassume_5fcheck : eo__24eo_5fpush_5fassume_5fcheck.Spec n
  eo__24eo_5fpush_5finput_5fassume_5fcheck : eo__24eo_5fpush_5finput_5fassume_5fcheck.Spec n
  eo__24eo_5fpush_5fproven_5fcheck : eo__24eo_5fpush_5fproven_5fcheck.Spec n
  eo__24eo_5fstate_5fis_5fclosed : eo__24eo_5fstate_5fis_5fclosed.Spec n
  eo__24eo_5fstate_5fis_5frefutation : eo__24eo_5fstate_5fis_5frefutation.Spec n
  eo__24eo_5fstate_5fproven_5fnth : eo__24eo_5fstate_5fproven_5fnth.Spec n
  eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff : eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff.Spec n
  eo__24eo_5fto_5fsmt_5fbv_5fsize : eo__24eo_5fto_5fsmt_5fbv_5fsize.Spec n
  eo__24eo_5fto_5fsmt_5fdatatype : eo__24eo_5fto_5fsmt_5fdatatype.Spec n
  eo__24eo_5fto_5fsmt_5fdatatype_5fcons : eo__24eo_5fto_5fsmt_5fdatatype_5fcons.Spec n
  eo__24eo_5fto_5fsmt_5fdatatype_5fdecl : eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.Spec n
  eo__24eo_5fto_5fsmt_5fexists : eo__24eo_5fto_5fsmt_5fexists.Spec n
  eo__24eo_5fto_5fsmt_5flambda_5fcurry : eo__24eo_5fto_5fsmt_5flambda_5fcurry.Spec n
  eo__24eo_5fto_5fsmt_5fnat : eo__24eo_5fto_5fsmt_5fnat.Spec n
  eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid : eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid.Spec n
  eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize : eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize.Spec n
  eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent : eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent.Spec n
  eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname : eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.Spec n
  eo__24eo_5fto_5fsmt_5fseq_2eempty : eo__24eo_5fto_5fsmt_5fseq_2eempty.Spec n
  eo__24eo_5fto_5fsmt_5fset_2eempty : eo__24eo_5fto_5fsmt_5fset_2eempty.Spec n
  eo__24eo_5fto_5fsmt_5fset_5felem_5ftype : eo__24eo_5fto_5fsmt_5fset_5felem_5ftype.Spec n
  eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff : eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff.Spec n
  eo__24eo_5fto_5fsmt_5ftester : eo__24eo_5fto_5fsmt_5ftester.Spec n
  eo__24eo_5fto_5fsmt_5ftuple_5fdecl : eo__24eo_5fto_5fsmt_5ftuple_5fdecl.Spec n
  eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec : eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec.Spec n
  eo__24eo_5fto_5fsmt_5ftuple_5fselect : eo__24eo_5fto_5fsmt_5ftuple_5fselect.Spec n
  eo__24eo_5fto_5fsmt_5ftype : eo__24eo_5fto_5fsmt_5ftype.Spec n
  eo__24eo_5fto_5fsmt_5ftype_5ftuple : eo__24eo_5fto_5fsmt_5ftype_5ftuple.Spec n
  eo__24eo_5fto_5fsmt_5fupdater_5frec : eo__24eo_5fto_5fsmt_5fupdater_5frec.Spec n
  eo__24eo_5ftypeof_5f_2b : eo__24eo_5ftypeof_5f_2b.Spec n
  eo__24eo_5ftypeof_5f_2f : eo__24eo_5ftypeof_5f_2f.Spec n
  eo__24eo_5ftypeof_5f_3c : eo__24eo_5ftypeof_5f_3c.Spec n
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
  eo__24eo_5ftypeof_5f_40from_5fbools : eo__24eo_5ftypeof_5f_40from_5fbools.Spec n
  eo__24eo_5ftypeof_5f_40purify : eo__24eo_5ftypeof_5f_40purify.Spec n
  eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize : eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize.Spec n
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
  eo__24eo_5ftypeof_5fabs : eo__24eo_5ftypeof_5fabs.Spec n
  eo__24eo_5ftypeof_5fapply : eo__24eo_5ftypeof_5fapply.Spec n
  eo__24eo_5ftypeof_5fbvand : eo__24eo_5ftypeof_5fbvand.Spec n
  eo__24eo_5ftypeof_5fbvcomp : eo__24eo_5ftypeof_5fbvcomp.Spec n
  eo__24eo_5ftypeof_5fbvite : eo__24eo_5ftypeof_5fbvite.Spec n
  eo__24eo_5ftypeof_5fbvnego : eo__24eo_5ftypeof_5fbvnego.Spec n
  eo__24eo_5ftypeof_5fbvnot : eo__24eo_5ftypeof_5fbvnot.Spec n
  eo__24eo_5ftypeof_5fbvredand : eo__24eo_5ftypeof_5fbvredand.Spec n
  eo__24eo_5ftypeof_5fbvult : eo__24eo_5ftypeof_5fbvult.Spec n
  eo__24eo_5ftypeof_5fconcat : eo__24eo_5ftypeof_5fconcat.Spec n
  eo__24eo_5ftypeof_5fdistinct : eo__24eo_5ftypeof_5fdistinct.Spec n
  eo__24eo_5ftypeof_5fdiv : eo__24eo_5ftypeof_5fdiv.Spec n
  eo__24eo_5ftypeof_5fdivisible : eo__24eo_5ftypeof_5fdivisible.Spec n
  eo__24eo_5ftypeof_5fdt_5fcons_5frec : eo__24eo_5ftypeof_5fdt_5fcons_5frec.Spec n
  eo__24eo_5ftypeof_5fdt_5fsel_5freturn : eo__24eo_5ftypeof_5fdt_5fsel_5freturn.Spec n
  eo__24eo_5ftypeof_5fextract : eo__24eo_5ftypeof_5fextract.Spec n
  eo__24eo_5ftypeof_5fforall : eo__24eo_5ftypeof_5fforall.Spec n
  eo__24eo_5ftypeof_5ffun_5ftype : eo__24eo_5ftypeof_5ffun_5ftype.Spec n
  eo__24eo_5ftypeof_5fint_2eispow2 : eo__24eo_5ftypeof_5fint_2eispow2.Spec n
  eo__24eo_5ftypeof_5fint_2epow2 : eo__24eo_5ftypeof_5fint_2epow2.Spec n
  eo__24eo_5ftypeof_5fint_5fto_5fbv : eo__24eo_5ftypeof_5fint_5fto_5fbv.Spec n
  eo__24eo_5ftypeof_5fis : eo__24eo_5ftypeof_5fis.Spec n
  eo__24eo_5ftypeof_5fis_5fint : eo__24eo_5ftypeof_5fis_5fint.Spec n
  eo__24eo_5ftypeof_5fite : eo__24eo_5ftypeof_5fite.Spec n
  eo__24eo_5ftypeof_5flambda : eo__24eo_5ftypeof_5flambda.Spec n
  eo__24eo_5ftypeof_5fnot : eo__24eo_5ftypeof_5fnot.Spec n
  eo__24eo_5ftypeof_5for : eo__24eo_5ftypeof_5for.Spec n
  eo__24eo_5ftypeof_5fre_2e_2a : eo__24eo_5ftypeof_5fre_2e_2a.Spec n
  eo__24eo_5ftypeof_5fre_2e_2b_2b : eo__24eo_5ftypeof_5fre_2e_2b_2b.Spec n
  eo__24eo_5ftypeof_5fre_2e_5e : eo__24eo_5ftypeof_5fre_2e_5e.Spec n
  eo__24eo_5ftypeof_5fre_2eloop : eo__24eo_5ftypeof_5fre_2eloop.Spec n
  eo__24eo_5ftypeof_5fre_2erange : eo__24eo_5ftypeof_5fre_2erange.Spec n
  eo__24eo_5ftypeof_5frepeat : eo__24eo_5ftypeof_5frepeat.Spec n
  eo__24eo_5ftypeof_5frotate_5fleft : eo__24eo_5ftypeof_5frotate_5fleft.Spec n
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
  eo__24eo_5ftypeof_5ftuple : eo__24eo_5ftypeof_5ftuple.Spec n
  eo__24eo_5ftypeof_5ftuple_2eselect : eo__24eo_5ftypeof_5ftuple_2eselect.Spec n
  eo__24eo_5ftypeof_5ftuple_2eupdate : eo__24eo_5ftypeof_5ftuple_2eupdate.Spec n
  eo__24eo_5ftypeof_5fupdate : eo__24eo_5ftypeof_5fupdate.Spec n
  eo__24eo_5ftypeof_5fzero_5fextend : eo__24eo_5ftypeof_5fzero_5fextend.Spec n
  eo__24extract_5fantec : eo__24extract_5fantec.Spec n
  eo__24extract_5fantec_5frec : eo__24extract_5fantec_5frec.Spec n
  eo__24from_5fclause : eo__24from_5fclause.Spec n
  eo__24get_5farg_5flist_5frec : eo__24get_5farg_5flist_5frec.Spec n
  eo__24get_5flambda_5ftype : eo__24get_5flambda_5ftype.Spec n
  eo__24get_5fnth_5fvar_5ftype : eo__24get_5fnth_5fvar_5ftype.Spec n
  eo__24get_5fvar_5ftype : eo__24get_5fvar_5ftype.Spec n
  eo__24greatest_5fint_5flt : eo__24greatest_5fint_5flt.Spec n
  eo__24iota_5frec : eo__24iota_5frec.Spec n
  eo__24is_5farith_5ftype : eo__24is_5farith_5ftype.Spec n
  eo__24is_5fpoly_5fnorm_5frel_5fconsts : eo__24is_5fpoly_5fnorm_5frel_5fconsts.Spec n
  eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel : eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel.Spec n
  eo__24is_5fseq_5fconst : eo__24is_5fseq_5fconst.Spec n
  eo__24is_5fseq_5fconst_5frec : eo__24is_5fseq_5fconst_5frec.Spec n
  eo__24least_5fint_5fgt : eo__24least_5fint_5fgt.Spec n
  eo__24lower_5fnot_5fand : eo__24lower_5fnot_5fand.Spec n
  eo__24mk_5farith_5fsum_5fub_5frec : eo__24mk_5farith_5fsum_5fub_5frec.Spec n
  eo__24mk_5farith_5ftrichotomy : eo__24mk_5farith_5ftrichotomy.Spec n
  eo__24mk_5fcong_5frhs : eo__24mk_5fcong_5frhs.Spec n
  eo__24mk_5fdistinct_5felim : eo__24mk_5fdistinct_5felim.Spec n
  eo__24mk_5fdistinct_5felim_5frec : eo__24mk_5fdistinct_5felim_5frec.Spec n
  eo__24mk_5fdt_5finst_5frec : eo__24mk_5fdt_5finst_5frec.Spec n
  eo__24mk_5fdt_5finst_5ftuple : eo__24mk_5fdt_5finst_5ftuple.Spec n
  eo__24mk_5fdt_5finst_5ftuple_5frec : eo__24mk_5fdt_5finst_5ftuple_5frec.Spec n
  eo__24mk_5fdt_5fsplit : eo__24mk_5fdt_5fsplit.Spec n
  eo__24mk_5fho_5fcong : eo__24mk_5fho_5fcong.Spec n
  eo__24mk_5fnary_5fcong_5frhs : eo__24mk_5fnary_5fcong_5frhs.Spec n
  eo__24mk_5fquant_5fmerge_5fprenex : eo__24mk_5fquant_5fmerge_5fprenex.Spec n
  eo__24mk_5fquant_5fminiscope_5fand : eo__24mk_5fquant_5fminiscope_5fand.Spec n
  eo__24mk_5fre_5fconcat : eo__24mk_5fre_5fconcat.Spec n
  eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed : eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed.Spec n
  eo__24mk_5fre_5funfold_5fpos : eo__24mk_5fre_5funfold_5fpos.Spec n
  eo__24mk_5fre_5funfold_5fpos_5fstar : eo__24mk_5fre_5funfold_5fpos_5fstar.Spec n
  eo__24mk_5fskolems : eo__24mk_5fskolems.Spec n
  eo__24mk_5fsymm : eo__24mk_5fsymm.Spec n
  eo__24mk_5ftrans : eo__24mk_5ftrans.Spec n
  eo__24pair_5ffirst : eo__24pair_5ffirst.Spec n
  eo__24pair_5fsecond : eo__24pair_5fsecond.Spec n
  eo__24poly_5fmod_5fcoeffs : eo__24poly_5fmod_5fcoeffs.Spec n
  eo__24poly_5fneg : eo__24poly_5fneg.Spec n
  eo__24re_5fconcat_5fmerge : eo__24re_5fconcat_5fmerge.Spec n
  eo__24re_5fis_5funbound_5fwildcard : eo__24re_5fis_5funbound_5fwildcard.Spec n
  eo__24re_5fnullable : eo__24re_5fnullable.Spec n
  eo__24re_5frev_5fcomp : eo__24re_5frev_5fcomp.Spec n
  eo__24re_5frev_5fmap_5frev : eo__24re_5frev_5fmap_5frev.Spec n
  eo__24re_5fsplit_5fstr_5fto_5fre : eo__24re_5fsplit_5fstr_5fto_5fre.Spec n
  eo__24re_5funfold_5fpos_5fconcat_5frec : eo__24re_5funfold_5fpos_5fconcat_5frec.Spec n
  eo__24run_5fprocess_5fscope : eo__24run_5fprocess_5fscope.Spec n
  eo__24seq_5felement_5fof_5funit : eo__24seq_5felement_5fof_5funit.Spec n
  eo__24seq_5fempty : eo__24seq_5fempty.Spec n
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
  eo__24smtx_5ftypeof_5fbv_5fop_5f2 : eo__24smtx_5ftypeof_5fbv_5fop_5f2.Spec n
  eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret : eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret.Spec n
  eo__24smtx_5ftypeof_5fconcat : eo__24smtx_5ftypeof_5fconcat.Spec n
  eo__24smtx_5ftypeof_5fdt_5fcons_5frec : eo__24smtx_5ftypeof_5fdt_5fcons_5frec.Spec n
  eo__24smtx_5ftypeof_5fextract : eo__24smtx_5ftypeof_5fextract.Spec n
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
  eo__24smtx_5ftypeof_5fsign_5fextend : eo__24smtx_5ftypeof_5fsign_5fextend.Spec n
  eo__24smtx_5ftypeof_5fstore : eo__24smtx_5ftypeof_5fstore.Spec n
  eo__24smtx_5ftypeof_5fstr_2eat : eo__24smtx_5ftypeof_5fstr_2eat.Spec n
  eo__24smtx_5ftypeof_5fstr_2eindexof : eo__24smtx_5ftypeof_5fstr_2eindexof.Spec n
  eo__24smtx_5ftypeof_5fstr_2esubstr : eo__24smtx_5ftypeof_5fstr_2esubstr.Spec n
  eo__24smtx_5ftypeof_5fstr_2eupdate : eo__24smtx_5ftypeof_5fstr_2eupdate.Spec n
  eo__24smtx_5ftypeof_5fzero_5fextend : eo__24smtx_5ftypeof_5fzero_5fextend.Spec n
  eo__24str_5farith_5fentail_5fsimple_5frec : eo__24str_5farith_5fentail_5fsimple_5frec.Spec n
  eo__24str_5ffixed_5flen_5fre : eo__24str_5ffixed_5flen_5fre.Spec n
  eo__24str_5fis_5fempty : eo__24str_5fis_5fempty.Spec n
  eo__24str_5fis_5fprefix_5fflat : eo__24str_5fis_5fprefix_5fflat.Spec n
  eo__24str_5fleq_5feval_5frec : eo__24str_5fleq_5feval_5frec.Spec n
  eo__24str_5fmembership_5fre : eo__24str_5fmembership_5fre.Spec n
  eo__24str_5fmembership_5fstr : eo__24str_5fmembership_5fstr.Spec n
  eo__24str_5fmk_5fext_5fdeq : eo__24str_5fmk_5fext_5fdeq.Spec n
  eo__24str_5fmk_5fre_5floop_5felim_5frec : eo__24str_5fmk_5fre_5floop_5felim_5frec.Spec n
  eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar : eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar.Spec n
  eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec : eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec.Spec n
  eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec : eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec.Spec n
  eo__24str_5fstrip_5fprefix : eo__24str_5fstrip_5fprefix.Spec n
  eo__24str_5fto_5fint_5feval_5frec : eo__24str_5fto_5fint_5feval_5frec.Spec n
  eo__24str_5funify_5fsplit : eo__24str_5funify_5fsplit.Spec n
  eo__24str_5fvalue_5flen : eo__24str_5fvalue_5flen.Spec n
  eo__24strip_5feven_5fexponent : eo__24strip_5feven_5fexponent.Spec n
  eo__24to_5fclause : eo__24to_5fclause.Spec n
  eo__24to_5fcube : eo__24to_5fcube.Spec n
  eo__24tuple_5farg_5flist : eo__24tuple_5farg_5flist.Spec n
  eo__24tuple_5fcollapse_5fupdater_5frhs : eo__24tuple_5fcollapse_5fupdater_5frhs.Spec n
  eo__24tuple_5fget_5fselectors_5frec : eo__24tuple_5fget_5fselectors_5frec.Spec n
  eo__24typed_5flist_5felement_5ftype : eo__24typed_5flist_5felement_5ftype.Spec n

end pathos_compiled_checker
