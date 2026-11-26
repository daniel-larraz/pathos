module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtTranslate
import all CpcMini.SmtTranslate
public import CpcMini.SmtModel
import all CpcMini.SmtModel
public import MiniCases
import all MiniCases
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
open generated generated.part0

/-- What is proved of `$eo_StateObj_proven`. -/
def eo__24eo_5fStateObj_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_StateObj_proven x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_checker_is_refutation`. -/
def eo__24eo_5fchecker_5fis_5frefutation.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fchecker_5fis_5frefutation s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_checker_is_refutation x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_cmd_step_pop_proven`. -/
def eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → StateOK x_a0 →
    eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_cmd_step_proven`. -/
def eo__24eo_5fcmd_5fstep_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → StateOK x_a0 →
    eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_cmd_step_proven x_a0 x_a1 x_a2 x_a3)
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

/-- What is proved of `$eo_invoke_assume_list`. -/
def eo__24eo_5finvoke_5fassume_5flist.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
    eo__24eo_5finvoke_5fassume_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_assume_list x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_invoke_cmd`. -/
def eo__24eo_5finvoke_5fcmd.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
    eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_invoke_cmd_check_proven`. -/
def eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
    eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_invoke_cmd_list`. -/
def eo__24eo_5finvoke_5fcmd_5flist.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
    eo__24eo_5finvoke_5fcmd_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_list x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_invoke_cmd_step_pop`. -/
def eo__24eo_5finvoke_5fcmd_5fstep_5fpop.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → StateOK x_a0 → StateOK x_a1 →
    eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_bool_type`. -/
def eo__24eo_5fis_5fbool_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5fbool_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_bool_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_closed`. -/
def eo__24eo_5fis_5fclosed.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_closed_rec`. -/
def eo__24eo_5fis_5fclosed_5frec.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fis_5fclosed_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_closed_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_is_list_nil`. -/
def eo__24eo_5fis_5flist_5fnil.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1)
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

/-- What is proved of `$eo_mk_premise_list`. -/
def eo__24eo_5fmk_5fpremise_5flist.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → StateOK x_a2 →
    eo__24eo_5fmk_5fpremise_5flist s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_mk_premise_list x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_nil`. -/
def eo__24eo_5fnil.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_prog_contra`. -/
def eo__24eo_5fprog_5fcontra.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_contra x_a0 x_a1)
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

/-- What is proved of `$eo_push_proven`. -/
def eo__24eo_5fpush_5fproven.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a1 →
    eo__24eo_5fpush_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_proven x_a0 x_a1)
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

/-- What is proved of `$eo_to_smt`. -/
def eo__24eo_5fto_5fsmt.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt x_a0)
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

/-- What is proved of `$eo_to_smt_reserved_datatype_name`. -/
def eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_reserved_datatype_name x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_to_smt_type`. -/
def eo__24eo_5fto_5fsmt_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_type x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof`. -/
def eo__24eo_5ftypeof.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof x_a0)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_=`. -/
def eo__24eo_5ftypeof_5f_3d.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_eq x_a0 x_a1)
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

/-- What is proved of `$eo_typeof_and`. -/
def eo__24eo_5ftypeof_5fand.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_and x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_apply`. -/
def eo__24eo_5ftypeof_5fapply.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_apply x_a0 x_a1)
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

/-- What is proved of `$eo_typeof_fun_type`. -/
def eo__24eo_5ftypeof_5ffun_5ftype.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5ftypeof_5ffun_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_fun_type x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- What is proved of `$eo_typeof_not`. -/
def eo__24eo_5ftypeof_5fnot.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24eo_5ftypeof_5fnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_not x_a0)
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

/-- What is proved of `$smtx_typeof`. -/
def eo__24smtx_5ftypeof.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 : Term) (x_a0 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 →
    eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof x_a0)
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

/-- What is proved of `$smtx_typeof_ite`. -/
def eo__24smtx_5ftypeof_5fite.Spec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
    eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div

@[simp] theorem Valid.var (x0 x1 : Eo.Term) :
    Valid.valid (Eo.Term.Var x0 x1) ↔
      x0 ≠ Eo.Term.Stuck ∧ Valid.valid x0 ∧ x1 ≠ Eo.Term.Stuck ∧ Valid.valid x1 := by
  show TreeValid (Embed.enc_Term _) ↔ _
  have hs : schema.Constructor.eo__24emb_5fVar.Strict := Or.inr rfl
  have he : ∀ x, Embed.enc_Term x = Tree.stuck ↔ x = Eo.Term.Stuck :=
    fun x => by simpa [Embed.embedded_enc_Term] using enc_eq_stuck_iff x
  have hv : ∀ x, Valid.valid x = TreeValid (Embed.enc_Term x) := fun _ => rfl
  simp only [Embed.enc_Term, TreeValid, TreesValid, and_true, hs, true_implies,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    ne_eq, he, hv]
  all_goals tauto

/-- What is proved of the programs, for stores that can enter `n` more calls. -/
structure Specs (n : Nat) : Prop where
  eo__24eo_5fStateObj_5fproven : eo__24eo_5fStateObj_5fproven.Spec n
  eo__24eo_5fchecker_5fis_5frefutation : eo__24eo_5fchecker_5fis_5frefutation.Spec n
  eo__24eo_5fcmd_5fstep_5fpop_5fproven : eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec n
  eo__24eo_5fcmd_5fstep_5fproven : eo__24eo_5fcmd_5fstep_5fproven.Spec n
  eo__24eo_5fdd_5flookup : eo__24eo_5fdd_5flookup.Spec n
  eo__24eo_5fdd_5fresolve : eo__24eo_5fdd_5fresolve.Spec n
  eo__24eo_5fdt_5fresolve : eo__24eo_5fdt_5fresolve.Spec n
  eo__24eo_5fdtc_5fresolve : eo__24eo_5fdtc_5fresolve.Spec n
  eo__24eo_5finvoke_5fassume_5flist : eo__24eo_5finvoke_5fassume_5flist.Spec n
  eo__24eo_5finvoke_5fcmd : eo__24eo_5finvoke_5fcmd.Spec n
  eo__24eo_5finvoke_5fcmd_5fcheck_5fproven : eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec n
  eo__24eo_5finvoke_5fcmd_5flist : eo__24eo_5finvoke_5fcmd_5flist.Spec n
  eo__24eo_5finvoke_5fcmd_5fstep_5fpop : eo__24eo_5finvoke_5fcmd_5fstep_5fpop.Spec n
  eo__24eo_5fis_5fbool_5ftype : eo__24eo_5fis_5fbool_5ftype.Spec n
  eo__24eo_5fis_5fclosed : eo__24eo_5fis_5fclosed.Spec n
  eo__24eo_5fis_5fclosed_5frec : eo__24eo_5fis_5fclosed_5frec.Spec n
  eo__24eo_5fis_5flist_5fnil : eo__24eo_5fis_5flist_5fnil.Spec n
  eo__24eo_5flit_5ftype_5fBinary : eo__24eo_5flit_5ftype_5fBinary.Spec n
  eo__24eo_5flit_5ftype_5fNumeral : eo__24eo_5flit_5ftype_5fNumeral.Spec n
  eo__24eo_5flit_5ftype_5fRational : eo__24eo_5flit_5ftype_5fRational.Spec n
  eo__24eo_5flit_5ftype_5fString : eo__24eo_5flit_5ftype_5fString.Spec n
  eo__24eo_5fmk_5fpremise_5flist : eo__24eo_5fmk_5fpremise_5flist.Spec n
  eo__24eo_5fnil : eo__24eo_5fnil.Spec n
  eo__24eo_5fprog_5fcontra : eo__24eo_5fprog_5fcontra.Spec n
  eo__24eo_5fprog_5frefl : eo__24eo_5fprog_5frefl.Spec n
  eo__24eo_5fprog_5fscope : eo__24eo_5fprog_5fscope.Spec n
  eo__24eo_5fprog_5fsymm : eo__24eo_5fprog_5fsymm.Spec n
  eo__24eo_5fprog_5ftrans : eo__24eo_5fprog_5ftrans.Spec n
  eo__24eo_5fpush_5fassume_5fcheck : eo__24eo_5fpush_5fassume_5fcheck.Spec n
  eo__24eo_5fpush_5finput_5fassume_5fcheck : eo__24eo_5fpush_5finput_5fassume_5fcheck.Spec n
  eo__24eo_5fpush_5fproven : eo__24eo_5fpush_5fproven.Spec n
  eo__24eo_5fpush_5fproven_5fcheck : eo__24eo_5fpush_5fproven_5fcheck.Spec n
  eo__24eo_5fstate_5fis_5fclosed : eo__24eo_5fstate_5fis_5fclosed.Spec n
  eo__24eo_5fstate_5fis_5frefutation : eo__24eo_5fstate_5fis_5frefutation.Spec n
  eo__24eo_5fstate_5fproven_5fnth : eo__24eo_5fstate_5fproven_5fnth.Spec n
  eo__24eo_5fto_5fsmt : eo__24eo_5fto_5fsmt.Spec n
  eo__24eo_5fto_5fsmt_5fdatatype : eo__24eo_5fto_5fsmt_5fdatatype.Spec n
  eo__24eo_5fto_5fsmt_5fdatatype_5fcons : eo__24eo_5fto_5fsmt_5fdatatype_5fcons.Spec n
  eo__24eo_5fto_5fsmt_5fdatatype_5fdecl : eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.Spec n
  eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname : eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.Spec n
  eo__24eo_5fto_5fsmt_5ftype : eo__24eo_5fto_5fsmt_5ftype.Spec n
  eo__24eo_5ftypeof : eo__24eo_5ftypeof.Spec n
  eo__24eo_5ftypeof_5f_3d : eo__24eo_5ftypeof_5f_3d.Spec n
  eo__24eo_5ftypeof_5fBitVec : eo__24eo_5ftypeof_5fBitVec.Spec n
  eo__24eo_5ftypeof_5fSeq : eo__24eo_5ftypeof_5fSeq.Spec n
  eo__24eo_5ftypeof_5fand : eo__24eo_5ftypeof_5fand.Spec n
  eo__24eo_5ftypeof_5fapply : eo__24eo_5ftypeof_5fapply.Spec n
  eo__24eo_5ftypeof_5fdt_5fcons_5frec : eo__24eo_5ftypeof_5fdt_5fcons_5frec.Spec n
  eo__24eo_5ftypeof_5fdt_5fsel_5freturn : eo__24eo_5ftypeof_5fdt_5fsel_5freturn.Spec n
  eo__24eo_5ftypeof_5ffun_5ftype : eo__24eo_5ftypeof_5ffun_5ftype.Spec n
  eo__24eo_5ftypeof_5fnot : eo__24eo_5ftypeof_5fnot.Spec n
  eo__24mk_5fsymm : eo__24mk_5fsymm.Spec n
  eo__24mk_5ftrans : eo__24mk_5ftrans.Spec n
  eo__24smtx_5fdd_5fhas_5fdt : eo__24smtx_5fdd_5fhas_5fdt.Spec n
  eo__24smtx_5fdd_5flookup : eo__24smtx_5fdd_5flookup.Spec n
  eo__24smtx_5fdecl_5finhabited : eo__24smtx_5fdecl_5finhabited.Spec n
  eo__24smtx_5fdecl_5fwf_5frec : eo__24smtx_5fdecl_5fwf_5frec.Spec n
  eo__24smtx_5fdt_5fcons_5finhabited : eo__24smtx_5fdt_5fcons_5finhabited.Spec n
  eo__24smtx_5fdt_5fcons_5fwf_5frec : eo__24smtx_5fdt_5fcons_5fwf_5frec.Spec n
  eo__24smtx_5fdt_5finhabited : eo__24smtx_5fdt_5finhabited.Spec n
  eo__24smtx_5fdt_5fresolve : eo__24smtx_5fdt_5fresolve.Spec n
  eo__24smtx_5fdt_5fwf_5frec : eo__24smtx_5fdt_5fwf_5frec.Spec n
  eo__24smtx_5fdtc_5fresolve : eo__24smtx_5fdtc_5fresolve.Spec n
  eo__24smtx_5finhabited_5ftype : eo__24smtx_5finhabited_5ftype.Spec n
  eo__24smtx_5fret_5ftypeof_5fsel : eo__24smtx_5fret_5ftypeof_5fsel.Spec n
  eo__24smtx_5fret_5ftypeof_5fsel_5frec : eo__24smtx_5fret_5ftypeof_5fsel_5frec.Spec n
  eo__24smtx_5ftype_5fwf : eo__24smtx_5ftype_5fwf.Spec n
  eo__24smtx_5ftype_5fwf_5fcomponent : eo__24smtx_5ftype_5fwf_5fcomponent.Spec n
  eo__24smtx_5ftype_5fwf_5frec : eo__24smtx_5ftype_5fwf_5frec.Spec n
  eo__24smtx_5ftypeof : eo__24smtx_5ftypeof.Spec n
  eo__24smtx_5ftypeof_5f_3d : eo__24smtx_5ftypeof_5f_3d.Spec n
  eo__24smtx_5ftypeof_5fapply : eo__24smtx_5ftypeof_5fapply.Spec n
  eo__24smtx_5ftypeof_5fdt_5fcons_5frec : eo__24smtx_5ftypeof_5fdt_5fcons_5frec.Spec n
  eo__24smtx_5ftypeof_5fguard : eo__24smtx_5ftypeof_5fguard.Spec n
  eo__24smtx_5ftypeof_5fguard_5fwf : eo__24smtx_5ftypeof_5fguard_5fwf.Spec n
  eo__24smtx_5ftypeof_5fite : eo__24smtx_5ftypeof_5fite.Spec n

theorem case_0_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_0
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_0 using

theorem case_1_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_1
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_1 using

theorem case_2_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eproven.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_2
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_2 using

/-- logos's `__eo_StateObj_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fStateObj_5fproven.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_StateObj_proven x_a0 =
      (firstSome [EoCases.__eo_StateObj_proven.case_0 x_a0, EoCases.__eo_StateObj_proven.case_1 x_a0, EoCases.__eo_StateObj_proven.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_StateObj_proven
  unfold EoCases.__eo_StateObj_proven.case_0 EoCases.__eo_StateObj_proven.case_1 EoCases.__eo_StateObj_proven.case_2
  logos_eq

theorem body_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_StateObj_proven x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fStateObj_5fproven.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fStateObj_5fproven_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fStateObj_5fproven_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  case_step with case_2_eo__24eo_5fStateObj_5fproven_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_StateObj_proven.case_0 EoCases.__eo_StateObj_proven.case_1 EoCases.__eo_StateObj_proven.case_2

theorem eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fStateObj_5fproven.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fStateObj_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fStateObj_5fproven s1 a0) (fun s' t => Represents.rep s' t (__eo_StateObj_proven x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fStateObj_5fproven_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fchecker_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fchecker_5fis_5frefutation s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_checker_is_refutation.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_checker_is_refutation.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fchecker_5fis_5frefutation
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24eo_5finvoke_5fassume_5flist s1 v0 a0 _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a0 (by good_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with ih.eo__24eo_5finvoke_5fcmd_5flist s2 v1 a1 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_a1 (by good_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with ih.eo__24eo_5fstate_5fis_5frefutation s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 (by good_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__eo_checker_is_refutation.case_0 using

/-- logos's `__eo_checker_is_refutation` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fchecker_5fis_5frefutation.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_checker_is_refutation x_a0 x_a1 =
      (firstSome [EoCases.__eo_checker_is_refutation.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_checker_is_refutation
  unfold EoCases.__eo_checker_is_refutation.case_0
  logos_eq

theorem body_eo__24eo_5fchecker_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fchecker_5fis_5frefutation s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_checker_is_refutation x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fchecker_5fis_5frefutation.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fchecker_5fis_5frefutation
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fchecker_5fis_5frefutation_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_checker_is_refutation.case_0 splitting x_a0 x_a1

theorem eo__24eo_5fchecker_5fis_5frefutation_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fchecker_5fis_5frefutation.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fchecker_5fis_5frefutation
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fchecker_5fis_5frefutation s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_checker_is_refutation x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fchecker_5fis_5frefutation_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fr_2escope.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fal_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5findl_2econs.destruct h_a4 as ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv2 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5findl_2enil.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4
  pat_same v4 v5 with h_v4 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  store_step with ih.eo__24eo_5fstate_5fproven_5fnth s3 a0 v3 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v3 (by good_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5
  have hn_v6 := state_proven_nth_ne_stuck_of h_v6 (by good_tac)
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fpf.construct s4 e_v7 (by rw [he_v7]; rfl) h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fprog_5fscope s5 a3 v7 _ _ hinv5 h64 (hG.rem hrem) h_a3 h_v7 (by good_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_cmd_step_pop_proven.case_0 using hn_v6

theorem case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.construct_stuck_spec s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  case_done hinv1 hG with h_v0 in EoCases.__eo_cmd_step_pop_proven.case_1 using

/-- logos's `__eo_cmd_step_pop_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fcmd_5fstep_5fpop_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4 =
      (firstSome [EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_cmd_step_pop_proven
  unfold EoCases.__eo_cmd_step_pop_proven.case_0 EoCases.__eo_cmd_step_pop_proven.case_1
  logos_eq

theorem body_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fcmd_5fstep_5fpop_5fproven.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using
  case_step with case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_cmd_step_pop_proven.case_0 EoCases.__eo_cmd_step_pop_proven.case_1

theorem eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
  unfold eo__24eo_5fcmd_5fstep_5fpop_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fcmd_5fstep_5fpop_5fproven s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fcmd_5fstep_5fproven more_0_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fr_2econtra.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_cmd_step_proven.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fal_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_cmd_step_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5findl_2econs.destruct h_a3 as ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv2 hG in EoCases.__eo_cmd_step_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5findl_2econs.destruct h_v4 as ⟨v6, x_v6, h_v6⟩ ⟨v7, x_v7, h_v7⟩ else hinv2 hG in EoCases.__eo_cmd_step_proven.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5findl_2enil.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v7 v8 with h_v7 h_v8 using hinv3 else hinv3 hG in EoCases.__eo_cmd_step_proven.case_0
  store_step with ih.eo__24eo_5fstate_5fproven_5fnth s3 a0 v3 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v3 (by good_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  have hn_v9 := state_proven_nth_ne_stuck_of h_v9 (by good_tac)
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24eo_5fpf.construct s4 e_v10 (by rw [he_v10]; rfl) h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5fstate_5fproven_5fnth s5 a0 v6 _ _ hinv5 h64 (hG.rem hrem) h_a0 h_v6 (by good_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10
  have hn_v11 := state_proven_nth_ne_stuck_of h_v11 (by good_tac)
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24eo_5fpf.construct s6 e_v12 (by rw [he_v12]; rfl) h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5fprog_5fcontra s7 v10 v12 _ _ hinv7 h64 (hG.rem hrem) h_v10 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv8 hG with h_v13 in EoCases.__eo_cmd_step_proven.case_0 using hn_v9 hn_v11

theorem case_1_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fr_2erefl.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_cmd_step_proven.case_1
  pat_destruct CtorSpec.eo__24emb_5fal_2econs.destruct h_a2 as ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv1 hG in EoCases.__eo_cmd_step_proven.case_1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fal_2enil.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v3
  pat_same v3 v4 with h_v3 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_cmd_step_proven.case_1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5findl_2enil.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v3 h_v4
  pat_same a3 v5 with h_a3 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_cmd_step_proven.case_1
  store_step with ih.eo__24eo_5fprog_5frefl s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__eo_cmd_step_proven.case_1 using

theorem case_2_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    case_2_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fr_2esymm.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_cmd_step_proven.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fal_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_cmd_step_proven.case_2
  pat_destruct CtorSpec.eo__24emb_5findl_2econs.destruct h_a3 as ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv2 hG in EoCases.__eo_cmd_step_proven.case_2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5findl_2enil.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4
  pat_same v4 v5 with h_v4 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_cmd_step_proven.case_2
  store_step with ih.eo__24eo_5fstate_5fproven_5fnth s3 a0 v3 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v3 (by good_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v5
  have hn_v6 := state_proven_nth_ne_stuck_of h_v6 (by good_tac)
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fpf.construct s4 e_v7 (by rw [he_v7]; rfl) h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fprog_5fsymm s5 v7 _ hinv5 h64 (hG.rem hrem) h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_cmd_step_proven.case_2 using hn_v6

theorem case_3_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    case_3_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fr_2etrans.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_cmd_step_proven.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fal_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_cmd_step_proven.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_and.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with ih.eo__24eo_5fmk_5fpremise_5flist s3 v2 a3 a0 _ _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a3 h_a0 (by good_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24eo_5fpf.construct s4 e_v4 (by rw [he_v4]; rfl) h_v3 hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fprog_5ftrans s5 v4 _ hinv5 h64 (hG.rem hrem) h_v4 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  case_done hinv6 hG with h_v5 in EoCases.__eo_cmd_step_proven.case_3 using

theorem case_4_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    case_4_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.construct_stuck_spec s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  case_done hinv1 hG with h_v0 in EoCases.__eo_cmd_step_proven.case_4 using

theorem cases_0_0_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    cases_0_0_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5fcmd_5fstep_5fproven_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24eo_5fcmd_5fstep_5fproven_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24eo_5fcmd_5fstep_5fproven_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hg_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24eo_5fcmd_5fstep_5fproven_spec n ih s3 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hg_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    cases_0_1_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5fcmd_5fstep_5fproven_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using
  group_none hinv1 hG with hl_4

/-- logos's `__eo_cmd_step_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fcmd_5fstep_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_cmd_step_proven x_a0 x_a1 x_a2 x_a3 =
      (firstSome [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_cmd_step_proven
  unfold EoCases.__eo_cmd_step_proven.case_0 EoCases.__eo_cmd_step_proven.case_1 EoCases.__eo_cmd_step_proven.case_2 EoCases.__eo_cmd_step_proven.case_3 EoCases.__eo_cmd_step_proven.case_4
  logos_eq

theorem body_eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fcmd_5fstep_5fproven s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_cmd_step_proven x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fcmd_5fstep_5fproven.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fcmd_5fstep_5fproven
  have hG := Store.Grows.refl s
  body_group_step with cases_0_0_eo__24eo_5fcmd_5fstep_5fproven_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_step with cases_0_1_eo__24eo_5fcmd_5fstep_5fproven_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] = [EoCases.__eo_cmd_step_proven.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_cmd_step_proven.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__eo_cmd_step_proven.case_4 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hl_0 hl_1 hl_2 hl_3 hl_4 in EoCases.__eo_cmd_step_proven.case_0 EoCases.__eo_cmd_step_proven.case_1 EoCases.__eo_cmd_step_proven.case_2 EoCases.__eo_cmd_step_proven.case_3 EoCases.__eo_cmd_step_proven.case_4

theorem eo__24eo_5fcmd_5fstep_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fcmd_5fstep_5fproven.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hg_a0
  unfold eo__24eo_5fcmd_5fstep_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fcmd_5fstep_5fproven s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_cmd_step_proven x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fcmd_5fstep_5fproven_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_lookup.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_lookup.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_dd_lookup.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_streq] at h_v4
  have h_ite_v6 := (show if_0_eo__24eo_5fdd_5flookup s1 v4 v2 a0 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fdd_5flookup
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_v2)
    · ite_branch hbv_5
      store_step with ih.eo__24eo_5fdd_5flookup s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__eo_dd_lookup.case_0 using

theorem case_1_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_lookup.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_lookup.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dd_lookup.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dd_lookup.case_1 using

/-- logos's `__eo_dd_lookup` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdd_5flookup.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dd_lookup x_a0 x_a1 =
      (firstSome [EoCases.__eo_dd_lookup.case_0 x_a0 x_a1, EoCases.__eo_dd_lookup.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dd_lookup
  unfold EoCases.__eo_dd_lookup.case_0 EoCases.__eo_dd_lookup.case_1
  logos_eq

theorem body_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_lookup x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdd_5flookup.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdd_5flookup_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdd_5flookup_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_dd_lookup.case_0 EoCases.__eo_dd_lookup.case_1 splitting x_a0 x_a1

theorem eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdd_5flookup.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdd_5flookup
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 6#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdd_5flookup s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dd_lookup x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_6 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_6 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdd_5flookup_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdd_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdd_5fresolve
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fdd_5flookup s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24eo_5fdt_5fresolve s1 v0 a1 _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dd_resolve.case_0 using

/-- logos's `__eo_dd_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdd_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dd_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dd_resolve.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dd_resolve
  unfold EoCases.__eo_dd_resolve.case_0
  logos_eq

theorem body_eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdd_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdd_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdd_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdd_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_dd_resolve.case_0 splitting x_a0 x_a1

theorem eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdd_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdd_5fresolve
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdd_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dd_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdd_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dt_resolve.case_0
  store_step with ih.eo__24eo_5fdtc_5fresolve s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24eo_5fdt_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fedt_2esum.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_dt_resolve.case_0 using

theorem case_1_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dt_resolve.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dt_resolve.case_1 using

/-- logos's `__eo_dt_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdt_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dt_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dt_resolve.case_0 x_a0 x_a1, EoCases.__eo_dt_resolve.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dt_resolve
  unfold EoCases.__eo_dt_resolve.case_0 EoCases.__eo_dt_resolve.case_1
  logos_eq

theorem body_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdt_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdt_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdt_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_dt_resolve.case_0 EoCases.__eo_dt_resolve.case_1 splitting x_a0 x_a1

theorem eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdt_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdt_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 10#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdt_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dt_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_10 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_10 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdt_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_0
  pat_destruct CtorSpec.eo__24emb_5fDatatypeTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fDatatypeType.construct s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fdtc_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2econs.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_dtc_resolve.case_0 using

theorem case_1_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_1
  store_step with ih.eo__24eo_5fdtc_5fresolve s v2 a1 _ _ hinv h64 hrem h_v2 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2econs.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_dtc_resolve.case_1 using

theorem case_2_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dtc_resolve.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dtc_resolve.case_2 using

/-- logos's `__eo_dtc_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdtc_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dtc_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1, EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1, EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dtc_resolve
  unfold EoCases.__eo_dtc_resolve.case_0 EoCases.__eo_dtc_resolve.case_1 EoCases.__eo_dtc_resolve.case_2
  logos_eq

theorem body_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dtc_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdtc_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdtc_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdtc_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24eo_5fdtc_5fresolve_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_dtc_resolve.case_0 EoCases.__eo_dtc_resolve.case_1 EoCases.__eo_dtc_resolve.case_2 splitting x_a0 x_a1

theorem eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdtc_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdtc_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 13#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdtc_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dtc_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_13 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_13 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdtc_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- `$eo_invoke_assume_list`, by the proof written by hand. -/
theorem eo__24eo_5finvoke_5fassume_5flist_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fassume_5flist.Spec n :=
  invoke_assume_list_spec n (fun m hm => (ih m hm).eo__24eo_5fis_5fbool_5ftype) (fun m hm => (ih m hm).eo__24eo_5fis_5fclosed) (fun m hm => (ih m hm).eo__24eo_5fpush_5finput_5fassume_5fcheck)

theorem case_0_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_invoke_cmd.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_invoke_cmd.case_0 using

theorem case_1_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fcmd_2eassume_5fpush.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_invoke_cmd.case_1
  store_step with ih.eo__24eo_5fis_5fbool_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  store_step with ih.eo__24eo_5fis_5fclosed s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_and s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fpush_5fassume_5fcheck s3 v4 v1 a0 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v1 h_a0 (by good_tac) as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v5 in EoCases.__eo_invoke_cmd.case_1 using

theorem case_2_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_2_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fcmd_2echeck_5fproven.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_invoke_cmd.case_2
  store_step with ih.eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 v1 _ _ hinv h64 hrem h_a0 h_v1 (by good_tac) as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_invoke_cmd.case_2 using

theorem case_3_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_3_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fcmd_2estep.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_invoke_cmd.case_3
  store_step with ih.eo__24eo_5fcmd_5fstep_5fproven s a0 v1 v2 v3 _ _ _ _ hinv h64 hrem h_a0 h_v1 h_v2 h_v3 (by good_tac) as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fpush_5fproven s1 v4 a0 _ _ hinv1 h64 (hG.rem hrem) h_v4 h_a0 (by good_tac) as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v5 in EoCases.__eo_invoke_cmd.case_3 using

theorem case_4_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_4_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fcmd_2estep_5fpop.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_invoke_cmd.case_4
  store_step with ih.eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a0 v1 v2 v3 _ _ _ _ _ hinv h64 hrem h_a0 h_a0 h_v1 h_v2 h_v3 (by good_tac) (by good_tac) as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv1 hG with h_v4 in EoCases.__eo_invoke_cmd.case_4 using

theorem cases_0_0_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    cases_0_0_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1 = none ∧ EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1 = none ∧ EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1 = none ∧ EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5finvoke_5fcmd_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] = [] ++ [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24eo_5finvoke_5fcmd_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] = [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24eo_5finvoke_5fcmd_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] = [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24eo_5finvoke_5fcmd_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] = [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    cases_0_1_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5finvoke_5fcmd_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] = [] ++ [EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using
  group_none hinv1 hG with hl_4

/-- logos's `__eo_invoke_cmd` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5finvoke_5fcmd.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_invoke_cmd x_a0 x_a1 =
      (firstSome [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_invoke_cmd
  unfold EoCases.__eo_invoke_cmd.case_0 EoCases.__eo_invoke_cmd.case_1 EoCases.__eo_invoke_cmd.case_2 EoCases.__eo_invoke_cmd.case_3 EoCases.__eo_invoke_cmd.case_4
  logos_eq

theorem body_eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5finvoke_5fcmd s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5finvoke_5fcmd.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5finvoke_5fcmd
  have hG := Store.Grows.refl s
  body_group_step with cases_0_0_eo__24eo_5finvoke_5fcmd_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] = [] ++ [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_step with cases_0_1_eo__24eo_5finvoke_5fcmd_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] = [EoCases.__eo_invoke_cmd.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_1 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_2 x_a0 x_a1, EoCases.__eo_invoke_cmd.case_3 x_a0 x_a1] ++ [EoCases.__eo_invoke_cmd.case_4 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hl_0 hl_1 hl_2 hl_3 hl_4 in EoCases.__eo_invoke_cmd.case_0 EoCases.__eo_invoke_cmd.case_1 EoCases.__eo_invoke_cmd.case_2 EoCases.__eo_invoke_cmd.case_3 EoCases.__eo_invoke_cmd.case_4 splitting x_a0 x_a1

theorem eo__24eo_5finvoke_5fcmd_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fcmd.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
  unfold eo__24eo_5finvoke_5fcmd
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5finvoke_5fcmd s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_invoke_cmd x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5finvoke_5fcmd_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_check_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eproven.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_invoke_cmd_check_proven.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_eq s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fpush_5fproven_5fcheck s1 v5 v4 v2 _ _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v4 h_v2 (by good_tac) as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__eo_invoke_cmd_check_proven.case_0 using

theorem case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_invoke_cmd_check_proven.case_1 using

/-- logos's `__eo_invoke_cmd_check_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_invoke_cmd_check_proven x_a0 x_a1 =
      (firstSome [EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_invoke_cmd_check_proven
  unfold EoCases.__eo_invoke_cmd_check_proven.case_0 EoCases.__eo_invoke_cmd_check_proven.case_1
  logos_eq

theorem body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_invoke_cmd_check_proven.case_0 EoCases.__eo_invoke_cmd_check_proven.case_1 splitting x_a0 x_a1

theorem eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
  unfold eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5finvoke_5fcmd_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5finvoke_5fcmd_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_list.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ StateOK y0 ∧
          EoCases.__eo_invoke_cmd_list.case_0 x_a0 x_a1 = some (__eo_invoke_cmd_list y0 y1)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_list.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5finvoke_5fcmd_5flist
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fcmdl_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_invoke_cmd_list.case_0
  case_done hinv1 hG with h_a0 in EoCases.__eo_invoke_cmd_list.case_0 using

theorem case_1_eo__24eo_5finvoke_5fcmd_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5finvoke_5fcmd_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_list.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ StateOK y0 ∧
          EoCases.__eo_invoke_cmd_list.case_1 x_a0 x_a1 = some (__eo_invoke_cmd_list y0 y1)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_list.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5finvoke_5fcmd_5flist
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fcmdl_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_list.case_1
  store_step with ih.eo__24eo_5finvoke_5fcmd s a0 v1 _ _ hinv h64 hrem h_a0 h_v1 (by good_tac) as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  case_again hinv1 hG with h_v3 h_v2 goods 1 in EoCases.__eo_invoke_cmd_list.case_1 using

/-- logos's `__eo_invoke_cmd_list` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5finvoke_5fcmd_5flist.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_invoke_cmd_list x_a0 x_a1 =
      (firstSome [EoCases.__eo_invoke_cmd_list.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd_list.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_invoke_cmd_list
  unfold EoCases.__eo_invoke_cmd_list.case_0 EoCases.__eo_invoke_cmd_list.case_1
  logos_eq

theorem step_eo__24eo_5finvoke_5fcmd_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    step_eo__24eo_5finvoke_5fcmd_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_invoke_cmd_list x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ StateOK y0 ∧
          __eo_invoke_cmd_list x_a0 x_a1 = __eo_invoke_cmd_list y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5finvoke_5fcmd_5flist.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24eo_5finvoke_5fcmd_5flist
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  round_step with case_0_eo__24eo_5finvoke_5fcmd_5flist_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using
  round_step with case_1_eo__24eo_5finvoke_5fcmd_5flist_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hc0
  round_stuck hinv3 hG using hc0 hc1 in EoCases.__eo_invoke_cmd_list.case_0 EoCases.__eo_invoke_cmd_list.case_1 splitting x_a0 x_a1

theorem body_eo__24eo_5finvoke_5fcmd_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5finvoke_5fcmd_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_list x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → StateOK x_a0 →
      body_eo__24eo_5finvoke_5fcmd_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_list x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1 hg_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1 hg_a0
  unfold body_eo__24eo_5finvoke_5fcmd_5flist body_eo__24eo_5finvoke_5fcmd_5flist_loop
  step with step_eo__24eo_5finvoke_5fcmd_5flist_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, hnext, hrep0, hrep1, hgood0, heq⟩ := hr
      simp only
      have hlen : next.length = 2 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 s1 y0 y1 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hgood0
      unfold body_eo__24eo_5finvoke_5fcmd_5flist at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5finvoke_5fcmd_5flist_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fcmd_5flist.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
  unfold eo__24eo_5finvoke_5fcmd_5flist
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5finvoke_5fcmd_5flist s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_invoke_cmd_list x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5finvoke_5fcmd_5flist_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__eo_invoke_cmd_step_pop y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_step_pop.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_invoke_cmd_step_pop.case_0
  store_step with ih.eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a2 a3 v4 a4 _ _ _ _ _ hinv h64 hrem h_a0 h_a2 h_a3 h_v4 h_a4 (by good_tac) as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fpush_5fproven s1 v5 v2 _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v2 (by good_tac) as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__eo_invoke_cmd_step_pop.case_0 using

theorem case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__eo_invoke_cmd_step_pop y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_step_pop.case_1
  case_again hinv hG with h_a0 h_v2 h_a2 h_a3 h_a4 goods 2 in EoCases.__eo_invoke_cmd_step_pop.case_1 using

theorem case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__eo_invoke_cmd_step_pop y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  case_done hinv1 hG with h_v0 in EoCases.__eo_invoke_cmd_step_pop.case_2 using

/-- logos's `__eo_invoke_cmd_step_pop` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5finvoke_5fcmd_5fstep_5fpop.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4 =
      (firstSome [EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4] default) := by
  conv => lhs; unfold __eo_invoke_cmd_step_pop
  unfold EoCases.__eo_invoke_cmd_step_pop.case_0 EoCases.__eo_invoke_cmd_step_pop.case_1 EoCases.__eo_invoke_cmd_step_pop.case_2
  logos_eq

theorem step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          __eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4 = __eo_invoke_cmd_step_pop y0 y1 y2 y3 y4
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5finvoke_5fcmd_5fstep_5fpop.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  round_step with case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using
  round_step with case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hc0
  round_step with case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s3 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hc0 hc1
  round_stuck hinv4 hG using hc0 hc1 hc2 in EoCases.__eo_invoke_cmd_step_pop.case_0 EoCases.__eo_invoke_cmd_step_pop.case_1 EoCases.__eo_invoke_cmd_step_pop.case_2 splitting x_a0 x_a1 x_a2 x_a3 x_a4

theorem body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 a4 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → StateOK x_a0 → StateOK x_a1 →
      body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 hk hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
  unfold body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_loop
  step with step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, u4, y4, hnext, hrep0, hrep1, hrep2, hrep3, hrep4, hgood0, hgood1, heq⟩ := hr
      simp only
      have hlen : next.length = 5 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      step as ⟨b3, hb3⟩
      obtain rfl : b3 = u3 := by simp [hb3, hnext]
      step as ⟨b4, hb4⟩
      obtain rfl : b4 = u4 := by simp [hb4, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 b4 s1 y0 y1 y2 y3 y4 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3  hrep4  hgood0  hgood1
      unfold body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fcmd_5fstep_5fpop.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
  unfold eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) hg_a0 hg_a1))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5fbool_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5fbool_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_bool_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_bool_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5fbool_5ftype
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5ftypeof s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_eq s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_bool_type.case_0 using hn_a0

/-- logos's `__eo_is_bool_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5fbool_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_bool_type x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_bool_type.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_bool_type
  unfold EoCases.__eo_is_bool_type.case_0
  logos_eq

theorem body_eo__24eo_5fis_5fbool_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5fbool_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_bool_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5fbool_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5fbool_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5fbool_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_bool_type.case_0

theorem eo__24eo_5fis_5fbool_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5fbool_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5fbool_5ftype
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5fbool_5ftype s1 a0) (fun s' t => Represents.rep s' t (__eo_is_bool_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5fbool_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_closed.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_closed.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5fclosed
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24eo_5fis_5fclosed_5frec s1 a0 v0 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_closed.case_0 using hn_a0

/-- logos's `__eo_is_closed` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5fclosed.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_closed x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_closed.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_closed
  unfold EoCases.__eo_is_closed.case_0
  logos_eq

theorem body_eo__24eo_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5fclosed.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5fclosed
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5fclosed_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_closed.case_0

theorem eo__24eo_5fis_5fclosed_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5fclosed.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5fclosed
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5fclosed s1 a0) (fun s' t => Represents.rep s' t (__eo_is_closed x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5fclosed_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5fclosed_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5fclosed_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_closed_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_closed_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5fclosed_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_is_closed_rec.case_0
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same a1 v3 with h_a1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_is_closed_rec.case_0
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_is_closed_rec.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24eo_5fis_5fclosed_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fis_5fclosed_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_closed_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_closed_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fis_5fclosed_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_is_closed_rec.case_1
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a0
  pat_unapply h_a1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_is_closed_rec.case_1
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_is_closed_rec.case_1
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_is_closed_rec.case_1
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s1 e_v10 (by rw [he_v10]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_eq s2 e_v11 (by rw [he_v11]; rfl) h_v10 h_v8 hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  have h_ite_v15 := (show if_0_eo__24eo_5fis_5fclosed_5frec s3 v11 v1 v2 v5 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fis_5fclosed_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v11 with ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩
    · ite_branch hbv_12
      store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
      ite_done hinv4 hG with (eo_ite_true_rep _ hx_12 h_v12)
    · ite_branch hbv_12
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo__24emb_5fVar.construct s3 e_v13 (by rw [he_v13]; rfl) h_v1 h_v2 hinv3 h64 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
      store_step with ih.eo__24eo_5fis_5fclosed_5frec s4 v13 v5 _ _ hinv4 h64 (hG.rem hrem) h_v13 h_v5 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v13
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_12 h_v14)
    · ite_branch hbv_12
      ite_stuck hinv3 hG with hx_12)
  store_step with h_ite_v15 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv4 hG with h_v15 in EoCases.__eo_is_closed_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_2_eo__24eo_5fis_5fclosed_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24eo_5fis_5fclosed_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_closed_rec.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_closed_rec.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fis_5fclosed_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_is_closed_rec.case_2
  store_step with ih.eo__24eo_5fis_5fclosed_5frec s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24eo_5fis_5fclosed_5frec s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_is_closed_rec.case_2 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_3_eo__24eo_5fis_5fclosed_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_3_eo__24eo_5fis_5fclosed_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_closed_rec.case_3 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_closed_rec.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fis_5fclosed_5frec
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_is_closed_rec.case_3 using hn_a0 hn_a1

/-- logos's `__eo_is_closed_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5fclosed_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_is_closed_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_closed_rec.case_0 x_a0 x_a1, EoCases.__eo_is_closed_rec.case_1 x_a0 x_a1, EoCases.__eo_is_closed_rec.case_2 x_a0 x_a1, EoCases.__eo_is_closed_rec.case_3 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_closed_rec
  unfold EoCases.__eo_is_closed_rec.case_0 EoCases.__eo_is_closed_rec.case_1 EoCases.__eo_is_closed_rec.case_2 EoCases.__eo_is_closed_rec.case_3
  logos_eq

theorem body_eo__24eo_5fis_5fclosed_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fis_5fclosed_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_closed_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5fclosed_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fis_5fclosed_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fis_5fclosed_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24eo_5fis_5fclosed_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  case_step with case_2_eo__24eo_5fis_5fclosed_5frec_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0 hc1
  case_step with case_3_eo__24eo_5fis_5fclosed_5frec_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hc0 hc1 hc2 hc3 in EoCases.__eo_is_closed_rec.case_0 EoCases.__eo_is_closed_rec.case_1 EoCases.__eo_is_closed_rec.case_2 EoCases.__eo_is_closed_rec.case_3

theorem eo__24eo_5fis_5fclosed_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5fclosed_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fis_5fclosed_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 21#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fis_5fclosed_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_is_closed_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_21 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_21 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5fclosed_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_0 using hn_a0 hn_a1

theorem case_1_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_1
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_1 using hn_a0 hn_a1

theorem case_2_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_is_list_nil.case_2 using hn_a0 hn_a1

/-- logos's `__eo_is_list_nil` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_is_list_nil x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil
  unfold EoCases.__eo_is_list_nil.case_0 EoCases.__eo_is_list_nil.case_1 EoCases.__eo_is_list_nil.case_2
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  case_step with case_2_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__eo_is_list_nil.case_0 EoCases.__eo_is_list_nil.case_1 EoCases.__eo_is_list_nil.case_2

theorem eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fis_5flist_5fnil
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5flit_5ftype_5fBinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fBinary s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_Binary.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_Binary.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fBinary
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_len s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_mk_rep s2 v0 v1 _ _ hinv2 h64 h_v0 h_v1 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_lit_type_Binary.case_0 using hn_a0

/-- logos's `__eo_lit_type_Binary` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fBinary.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_Binary x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_Binary.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_Binary
  unfold EoCases.__eo_lit_type_Binary.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fBinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fBinary s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Binary x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fBinary.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fBinary
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fBinary_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_Binary.case_0

theorem eo__24eo_5flit_5ftype_5fBinary_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fBinary.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fBinary
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fBinary s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_Binary x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fBinary_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5flit_5ftype_5fNumeral_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fNumeral s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_Numeral.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_Numeral.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fNumeral
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_lit_type_Numeral.case_0 using hn_a0

/-- logos's `__eo_lit_type_Numeral` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fNumeral.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_Numeral x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_Numeral.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_Numeral
  unfold EoCases.__eo_lit_type_Numeral.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fNumeral_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fNumeral s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Numeral x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fNumeral.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fNumeral
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fNumeral_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_Numeral.case_0

theorem eo__24eo_5flit_5ftype_5fNumeral_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fNumeral.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fNumeral
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fNumeral s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_Numeral x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fNumeral_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5flit_5ftype_5fRational_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fRational s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_Rational.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_Rational.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fRational
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_lit_type_Rational.case_0 using hn_a0

/-- logos's `__eo_lit_type_Rational` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fRational.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_Rational x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_Rational.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_Rational
  unfold EoCases.__eo_lit_type_Rational.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fRational_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fRational s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Rational x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fRational.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fRational
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fRational_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_Rational.case_0

theorem eo__24eo_5flit_5ftype_5fRational_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fRational.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fRational
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fRational s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_Rational x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fRational_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5flit_5ftype_5fString_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fString s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_String.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_String.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fString
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Seq.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Char.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v0 v1 _ _ hinv2 h64 h_v0 h_v1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_lit_type_String.case_0 using hn_a0

/-- logos's `__eo_lit_type_String` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fString.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_String x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_String.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_String
  unfold EoCases.__eo_lit_type_String.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fString_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fString s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_String x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fString.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fString
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fString_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_String.case_0

theorem eo__24eo_5flit_5ftype_5fString_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fString.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fString
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fString s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_String x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fString_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fmk_5fpremise_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fmk_5fpremise_5flist s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_mk_premise_list.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_mk_premise_list.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fmk_5fpremise_5flist
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5findl_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_mk_premise_list.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with ih.eo__24eo_5fnil s2 a0 v1 _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v1 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_mk_premise_list.case_0 using

theorem case_1_eo__24eo_5fmk_5fpremise_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fmk_5fpremise_5flist s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_mk_premise_list.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_mk_premise_list.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fmk_5fpremise_5flist
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5findl_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_mk_premise_list.case_1
  store_step with ih.eo__24eo_5fstate_5fproven_5fnth s a2 v1 _ _ hinv h64 hrem h_a2 h_v1 (by good_tac) as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  have hn_v3 := state_proven_nth_ne_stuck_of h_v3 (by good_tac)
  store_step with ih.eo__24eo_5fmk_5fpremise_5flist s1 a0 v2 a2 _ _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v2 h_a2 (by good_tac) as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_cons n ih.eo__24eo_5fis_5flist_5fnil s2 e_v5 (by rw [he_v5]; rfl) h_a0 h_v3 h_v4 (by ns_tac) hinv2 h64 (hG.rem hrem) (by not_left_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_mk_premise_list.case_1 using hn_v3

/-- logos's `__eo_mk_premise_list` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fmk_5fpremise_5flist.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_mk_premise_list x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_mk_premise_list.case_0 x_a0 x_a1 x_a2, EoCases.__eo_mk_premise_list.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_mk_premise_list
  unfold EoCases.__eo_mk_premise_list.case_0 EoCases.__eo_mk_premise_list.case_1
  logos_eq

theorem body_eo__24eo_5fmk_5fpremise_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fmk_5fpremise_5flist s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_mk_premise_list x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fmk_5fpremise_5flist.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fmk_5fpremise_5flist
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fmk_5fpremise_5flist_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fmk_5fpremise_5flist_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_mk_premise_list.case_0 EoCases.__eo_mk_premise_list.case_1

theorem eo__24eo_5fmk_5fpremise_5flist_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fmk_5fpremise_5flist.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fmk_5fpremise_5flist
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fmk_5fpremise_5flist s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_mk_premise_list x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fmk_5fpremise_5flist_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_nil.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_nil.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_nil.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_nil.case_0 using hn_a0 hn_a1

theorem case_1_eo__24eo_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_nil.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_nil.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_nil.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_nil.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_nil.case_1 using hn_a0 hn_a1

/-- logos's `__eo_nil` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fnil.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_nil x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_nil.case_0 x_a0 x_a1, EoCases.__eo_nil.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_nil
  unfold EoCases.__eo_nil.case_0 EoCases.__eo_nil.case_1
  logos_eq

theorem body_eo__24eo_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fnil.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fnil
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24eo_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__eo_nil.case_0 EoCases.__eo_nil.case_1

theorem eo__24eo_5fnil_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fnil.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fnil
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fnil s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_nil x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fnil_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcontra_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_contra.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_contra.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcontra
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_contra.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_prog_contra.case_0
  pat_unapply h_v3 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv else hinv hG in EoCases.__eo_prog_contra.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_not.construct s e_v7 (by rw [he_v7]; exact empty_args) hinv h64 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v5 h_v6
  pat_same v5 v7 with h_v5 h_v7 using hinv1 else hinv1 hG in EoCases.__eo_prog_contra.case_0
  pat_same v6 v1 with h_v6 h_v1 using hinv1 else hinv1 hG in EoCases.__eo_prog_contra.case_0
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v5 h_v6 h_v7
  case_done hinv2 hG with h_v8 in EoCases.__eo_prog_contra.case_0 using hn_v5 hn_v6

/-- logos's `__eo_prog_contra` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcontra.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_contra x_a0 x_a1 =
      (firstSome [EoCases.__eo_prog_contra.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_contra
  unfold EoCases.__eo_prog_contra.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcontra_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_contra x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcontra.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fcontra
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fcontra_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_contra.case_0

theorem eo__24eo_5fprog_5fcontra_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcontra.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fcontra
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcontra s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_contra x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcontra_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5frefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5frefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_refl.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_refl.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5frefl
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_prog_refl.case_0 using hn_a0

/-- logos's `__eo_prog_refl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5frefl.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_refl x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_refl.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_refl
  unfold EoCases.__eo_prog_refl.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5frefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5frefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_refl x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5frefl.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5frefl
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5frefl_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_refl.case_0

theorem eo__24eo_5fprog_5frefl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5frefl.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5frefl
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5frefl s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_refl x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5frefl_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a1 : ProofOK x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_scope.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_scope.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fscope
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_scope.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  store_step with Store.apply_rep s1 v2 a0 _ _ hinv1 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  have hn_v1 := hg_a1 _ rfl
  store_step with Store.apply_rep s2 v3 v1 _ _ hinv2 h64 h_v3 h_v1 (by ns_tac) (by ns_tac) as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__eo_prog_scope.case_0 using hn_a0 hn_v1

/-- logos's `__eo_prog_scope` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fscope.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_scope x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_scope.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_scope
  unfold EoCases.__eo_prog_scope.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a1 : ProofOK x_a1) :
    body_eo__24eo_5fprog_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_scope x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fscope.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fscope
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fscope_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_scope.case_0

theorem eo__24eo_5fprog_5fscope_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fscope.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a1
  unfold eo__24eo_5fprog_5fscope
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fscope s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_scope x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fscope_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a1))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_symm.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_symm.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsymm
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_symm.case_0
  store_step with ih.eo__24mk_5fsymm s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_prog_symm.case_0 using

/-- logos's `__eo_prog_symm` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsymm.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_symm x_a0 =
      (firstSome [EoCases.__eo_prog_symm.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_symm
  unfold EoCases.__eo_prog_symm.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_symm x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsymm.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsymm
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fsymm_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_symm.case_0

theorem eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsymm.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsymm
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsymm s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_symm x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsymm_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ftrans s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_trans.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_trans.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrans
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_trans.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_and.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_trans.case_0
  store_step with ih.eo__24mk_5ftrans s2 v14 v11 v4 _ _ _ hinv2 h64 (hG.rem hrem) h_v14 h_v11 h_v4 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  case_done hinv3 hG with h_v16 in EoCases.__eo_prog_trans.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_trans` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrans.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_trans x_a0 =
      (firstSome [EoCases.__eo_prog_trans.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_trans
  unfold EoCases.__eo_prog_trans.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ftrans s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_trans x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrans.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ftrans
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ftrans_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_trans.case_0

theorem eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrans.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ftrans
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrans s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_trans x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrans_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_assume_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eassume_5fpush.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_assume_check.case_0 using

theorem case_1_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_assume_check.case_1 using

/-- logos's `__eo_push_assume_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fassume_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_assume_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_assume_check
  unfold EoCases.__eo_push_assume_check.case_0 EoCases.__eo_push_assume_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fassume_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fassume_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5fassume_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_assume_check.case_0 EoCases.__eo_push_assume_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fassume_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5fassume_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fassume_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_assume_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fassume_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_input_assume_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eassume.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_input_assume_check.case_0 using

theorem case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_input_assume_check.case_1 using

/-- logos's `__eo_push_input_assume_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5finput_5fassume_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_input_assume_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_input_assume_check
  unfold EoCases.__eo_push_input_assume_check.case_0 EoCases.__eo_push_input_assume_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_input_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5finput_5fassume_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_input_assume_check.case_0 EoCases.__eo_push_input_assume_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5finput_5fassume_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5finput_5fassume_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5finput_5fassume_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_input_assume_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a1 : StateOK x_a1) :
    case_0_eo__24eo_5fpush_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fproven
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fis_5fbool_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24eo_5fpush_5fproven_5fcheck s1 v0 a0 a1 _ _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a0 h_a1 (by good_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_push_proven.case_0 using

/-- logos's `__eo_push_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_push_proven x_a0 x_a1 =
      (firstSome [EoCases.__eo_push_proven.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_push_proven
  unfold EoCases.__eo_push_proven.case_0
  logos_eq

theorem body_eo__24eo_5fpush_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a1 : StateOK x_a1) :
    body_eo__24eo_5fpush_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_proven x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fproven.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fpush_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fproven_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_push_proven.case_0 splitting x_a0 x_a1

theorem eo__24eo_5fpush_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fproven.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a1
  unfold eo__24eo_5fpush_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fproven s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_push_proven x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fproven_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a1))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_proven_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eproven.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_proven_check.case_0 using

theorem case_1_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_proven_check.case_1 using

/-- logos's `__eo_push_proven_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fproven_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_proven_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_proven_check
  unfold EoCases.__eo_push_proven_check.case_0 EoCases.__eo_push_proven_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_proven_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fproven_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fproven_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5fproven_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_proven_check.case_0 EoCases.__eo_push_proven_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fproven_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5fproven_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fproven_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_proven_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fproven_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_0 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_state_is_closed.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_state_is_closed.case_0
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  case_done hinv1 hG with h_v5 in EoCases.__eo_state_is_closed.case_0 using

theorem case_1_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_1 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_state_is_closed.case_1
  case_again hinv hG with h_v2 goods 1 in EoCases.__eo_state_is_closed.case_1 using

theorem case_2_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_2_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_2 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_state_is_closed.case_2
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_state_is_closed.case_2 using

theorem case_3_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_3_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_3 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_state_is_closed.case_3 using

/-- logos's `__eo_state_is_closed` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fstate_5fis_5fclosed.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_state_is_closed x_a0 =
      (firstSome [EoCases.__eo_state_is_closed.case_0 x_a0, EoCases.__eo_state_is_closed.case_1 x_a0, EoCases.__eo_state_is_closed.case_2 x_a0, EoCases.__eo_state_is_closed.case_3 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_state_is_closed
  unfold EoCases.__eo_state_is_closed.case_0 EoCases.__eo_state_is_closed.case_1 EoCases.__eo_state_is_closed.case_2 EoCases.__eo_state_is_closed.case_3
  logos_eq

theorem step_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    step_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          __eo_state_is_closed x_a0 = __eo_state_is_closed y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fstate_5fis_5fclosed.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  round_step with case_0_eo__24eo_5fstate_5fis_5fclosed_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using
  round_step with case_1_eo__24eo_5fstate_5fis_5fclosed_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hc0
  round_step with case_2_eo__24eo_5fstate_5fis_5fclosed_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 hbud using hc0 hc1
  round_step with case_3_eo__24eo_5fstate_5fis_5fclosed_spec n ih s4 a0 x_a0 hinv4 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 hbud using hc0 hc1 hc2
  round_stuck hinv5 hG using hc0 hc1 hc2 hc3 in EoCases.__eo_state_is_closed.case_0 EoCases.__eo_state_is_closed.case_1 EoCases.__eo_state_is_closed.case_2 EoCases.__eo_state_is_closed.case_3 splitting x_a0

theorem body_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → StateOK x_a0 →
      body_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0 hg_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0 hg_a0
  unfold body_eo__24eo_5fstate_5fis_5fclosed body_eo__24eo_5fstate_5fis_5fclosed_loop
  step with step_eo__24eo_5fstate_5fis_5fclosed_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, hnext, hrep0, hgood0, heq⟩ := hr
      simp only
      have hlen : next.length = 1 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      have hrec := ihl s1.budget (by omega) b0 s1 y0 le_rfl hinv1 (hg1.rem hrem)  hrep0  hgood0
      unfold body_eo__24eo_5fstate_5fis_5fclosed at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fis_5fclosed.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fstate_5fis_5fclosed
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fstate_5fis_5fclosed s1 a0) (fun s' t => Represents.rep s' t (__eo_state_is_closed x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fstate_5fis_5fclosed_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fstate_5fis_5frefutation s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_state_is_refutation.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_state_is_refutation.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fstate_5fis_5frefutation
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s1 a0 v0 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v0 (by good_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with ih.eo__24eo_5fstate_5fis_5fclosed s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 (by good_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_state_is_refutation.case_0 using

/-- logos's `__eo_state_is_refutation` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fstate_5fis_5frefutation.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_state_is_refutation x_a0 =
      (firstSome [EoCases.__eo_state_is_refutation.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_state_is_refutation
  unfold EoCases.__eo_state_is_refutation.case_0
  logos_eq

theorem body_eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fstate_5fis_5frefutation s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_refutation x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fstate_5fis_5frefutation.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fstate_5fis_5frefutation
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fstate_5fis_5frefutation_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_state_is_refutation.case_0 splitting x_a0

theorem eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fis_5frefutation.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fstate_5fis_5frefutation
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fstate_5fis_5frefutation s1 a0) (fun s' t => Represents.rep s' t (__eo_state_is_refutation x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fstate_5fis_5frefutation_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- `$eo_state_proven_nth`, by the proof written by hand. -/
theorem eo__24eo_5fstate_5fproven_5fnth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fproven_5fnth.Spec n :=
  state_proven_nth_spec n (fun m hm => (ih m hm).eo__24eo_5fStateObj_5fproven)

theorem case_0_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_boolean_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_to_smt.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBoolean.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_numeral_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_to_smt.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_1 using

theorem case_2_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_rational_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_to_smt.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eRational.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_2 using

theorem case_3_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_string_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_to_smt.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eString.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_3 using

theorem case_4_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit2 Store.destruct_binary_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_to_smt.case_4
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s1 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__eo_to_smt.case_4 using

theorem case_5_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt.case_5
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a0
  pat_destruct_lit Store.destruct_string_spec s v1 h_v1 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_v1 h_v2 in EoCases.__eo_to_smt.case_5
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eVar.construct s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__eo_to_smt.case_5 using hn_v1 hn_v2

theorem case_6_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt.case_6
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v8 := (show if_0_eo__24eo_5fto_5fsmt s1 v4 v2 v1 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eDtCons.construct s2 e_v7 (by rw [he_v7]; rfl) h_v1 h_v6 h_v3 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v6
      ite_done hinv3 hG with (native_ite_false_rep _ hx_5 h_v7))
  store_step with h_ite_v8 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v8 in EoCases.__eo_to_smt.case_6 using

theorem case_7_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtSel.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_7
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v9 := (show if_1_eo__24eo_5fto_5fsmt s1 v5 v2 v1 v3 v4 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv2 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eDtSel.construct s2 e_v8 (by rw [he_v8]; rfl) h_v1 h_v7 h_v3 h_v4 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v7
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v8))
  store_step with h_ite_v9 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv2 hG with h_v9 in EoCases.__eo_to_smt.case_7 using

theorem case_8_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUConst.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt.case_8
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_uconst_id s e_v3 (by rw [he_v3]; rfl) h_v1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  rw [← Bridge.native_uconst_id] at h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eUConst.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_8 using

theorem case_9_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_9
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_9
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2enot.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_9 using hn_v1 hn_v2

theorem case_10_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_10_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_10
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_10
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_10
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eand.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_10 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_11_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_11_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_11
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_11
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_11
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d_3e.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_11 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_12_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_12_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_12
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_12
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_12
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_12 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_13_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_13_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_13
  store_step with ih.eo__24eo_5fto_5fsmt s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_13 using hn_v1 hn_v2

theorem case_14_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_14_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt.case_14 using

theorem cases_0_0_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_0 x_a0 = none ∧ EoCases.__eo_to_smt.case_1 x_a0 = none ∧ EoCases.__eo_to_smt.case_2 x_a0 = none ∧ EoCases.__eo_to_smt.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [] ++ [EoCases.__eo_to_smt.case_0 x_a0] ++ [EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0] ++ [EoCases.__eo_to_smt.case_1 x_a0] ++ [EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0] ++ [EoCases.__eo_to_smt.case_2 x_a0] ++ [EoCases.__eo_to_smt.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0] ++ [EoCases.__eo_to_smt.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_4 x_a0 = none ∧ EoCases.__eo_to_smt.case_5 x_a0 = none ∧ EoCases.__eo_to_smt.case_6 x_a0 = none ∧ EoCases.__eo_to_smt.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [] ++ [EoCases.__eo_to_smt.case_4 x_a0] ++ [EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [EoCases.__eo_to_smt.case_4 x_a0] ++ [EoCases.__eo_to_smt.case_5 x_a0] ++ [EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0] ++ [EoCases.__eo_to_smt.case_6 x_a0] ++ [EoCases.__eo_to_smt.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0] ++ [EoCases.__eo_to_smt.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_8 x_a0 = none ∧ EoCases.__eo_to_smt.case_9 x_a0 = none ∧ EoCases.__eo_to_smt.case_10 x_a0 = none ∧ EoCases.__eo_to_smt.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [] ++ [EoCases.__eo_to_smt.case_8 x_a0] ++ [EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [EoCases.__eo_to_smt.case_8 x_a0] ++ [EoCases.__eo_to_smt.case_9 x_a0] ++ [EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_step with case_10_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0] ++ [EoCases.__eo_to_smt.case_10 x_a0] ++ [EoCases.__eo_to_smt.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hl_8 hl_9
  group_step with case_11_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0] ++ [EoCases.__eo_to_smt.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_3_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_12 x_a0 = none ∧ EoCases.__eo_to_smt.case_13 x_a0 = none ∧ EoCases.__eo_to_smt.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] = [] ++ [EoCases.__eo_to_smt.case_12 x_a0] ++ [EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using
  group_step with case_13_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] = [EoCases.__eo_to_smt.case_12 x_a0] ++ [EoCases.__eo_to_smt.case_13 x_a0] ++ [EoCases.__eo_to_smt.case_14 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hl_12
  group_step with case_14_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] = [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0] ++ [EoCases.__eo_to_smt.case_14 x_a0] ++ [] from rfl)
    otherwise ⟨hl_14⟩ using hl_12 hl_13
  group_none hinv3 hG with ⟨hl_12, hl_13, hl_14⟩

/-- logos's `__eo_to_smt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt x_a0 =
      (firstSome [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt
  unfold EoCases.__eo_to_smt.case_0 EoCases.__eo_to_smt.case_1 EoCases.__eo_to_smt.case_2 EoCases.__eo_to_smt.case_3 EoCases.__eo_to_smt.case_4 EoCases.__eo_to_smt.case_5 EoCases.__eo_to_smt.case_6 EoCases.__eo_to_smt.case_7 EoCases.__eo_to_smt.case_8 EoCases.__eo_to_smt.case_9 EoCases.__eo_to_smt.case_10 EoCases.__eo_to_smt.case_11 EoCases.__eo_to_smt.case_12 EoCases.__eo_to_smt.case_13 EoCases.__eo_to_smt.case_14
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  body_group_step with cases_0_0_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] = [] ++ [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] ++ [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_step with cases_0_1_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] ++ [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] ++ [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] ++ [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] ++ [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_group_step with cases_0_3_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] ++ [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  body_stuck hinv4 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 in EoCases.__eo_to_smt.case_0 EoCases.__eo_to_smt.case_1 EoCases.__eo_to_smt.case_2 EoCases.__eo_to_smt.case_3 EoCases.__eo_to_smt.case_4 EoCases.__eo_to_smt.case_5 EoCases.__eo_to_smt.case_6 EoCases.__eo_to_smt.case_7 EoCases.__eo_to_smt.case_8 EoCases.__eo_to_smt.case_9 EoCases.__eo_to_smt.case_10 EoCases.__eo_to_smt.case_11 EoCases.__eo_to_smt.case_12 EoCases.__eo_to_smt.case_13 EoCases.__eo_to_smt.case_14 splitting x_a0

theorem eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 41#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_41 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_41 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fdatatype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fdatatype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_datatype.case_0
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fcons s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt_datatype.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fdatatype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fdatatype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_datatype.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_datatype.case_1 using

/-- logos's `__eo_to_smt_datatype` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fdatatype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_datatype x_a0 =
      (firstSome [EoCases.__eo_to_smt_datatype.case_0 x_a0, EoCases.__eo_to_smt_datatype.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_datatype
  unfold EoCases.__eo_to_smt_datatype.case_0 EoCases.__eo_to_smt_datatype.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fdatatype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fdatatype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fdatatype
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fdatatype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fdatatype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_datatype.case_0 EoCases.__eo_to_smt_datatype.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fdatatype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fdatatype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 42#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fdatatype s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_datatype x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_42 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_42 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fdatatype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_cons.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_cons.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_datatype_cons.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_datatype_cons.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_cons.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_cons.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_datatype_cons.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fcons s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2econs.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt_datatype_cons.case_1 using

/-- logos's `__eo_to_smt_datatype_cons` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fdatatype_5fcons.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_datatype_cons x_a0 =
      (firstSome [EoCases.__eo_to_smt_datatype_cons.case_0 x_a0, EoCases.__eo_to_smt_datatype_cons.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_datatype_cons
  unfold EoCases.__eo_to_smt_datatype_cons.case_0 EoCases.__eo_to_smt_datatype_cons.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype_cons x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fdatatype_5fcons.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_datatype_cons.case_0 EoCases.__eo_to_smt_datatype_cons.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fdatatype_5fcons.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 43#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_datatype_cons x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_43 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_43 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_decl.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_decl.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedd_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt_datatype_decl.case_0
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype s v2 _ hinv h64 hrem h_v2 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v3 _ hinv1 h64 (hG.rem hrem) h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fdd_2econs.construct s2 e_v6 (by rw [he_v6]; rfl) h_v1 h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__eo_to_smt_datatype_decl.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_decl.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_decl.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_datatype_decl.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_datatype_decl.case_1 using

/-- logos's `__eo_to_smt_datatype_decl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_datatype_decl x_a0 =
      (firstSome [EoCases.__eo_to_smt_datatype_decl.case_0 x_a0, EoCases.__eo_to_smt_datatype_decl.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_datatype_decl
  unfold EoCases.__eo_to_smt_datatype_decl.case_0 EoCases.__eo_to_smt_datatype_decl.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype_decl x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_datatype_decl.case_0 EoCases.__eo_to_smt_datatype_decl.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 44#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_datatype_decl x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_44 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_44 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_reserved_datatype_name.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_reserved_datatype_name.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s _ _ rfl hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  replace h_v0 := Represents.rep_of_eq h_v0 (y := SmtEval.native_string_lit "@") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v0]; decide)
  step as ⟨e_v1, he_v1⟩
  store_step with Store.native_spec_string_prefix_eq s1 e_v1 (by rw [he_v1]; rfl) h_v0 h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  rw [← Bridge.native_string_prefix_eq] at h_v1
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_reserved_datatype_name.case_0 using

/-- logos's `__eo_to_smt_reserved_datatype_name` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_reserved_datatype_name x_a0 =
      (firstSome [EoCases.__eo_to_smt_reserved_datatype_name.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_to_smt_reserved_datatype_name
  unfold EoCases.__eo_to_smt_reserved_datatype_name.case_0
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_reserved_datatype_name x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_to_smt_reserved_datatype_name.case_0 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_reserved_datatype_name x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDatatypeType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_type.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  have h_ite_v7 := (show if_0_eo__24eo_5fto_5fsmt_5ftype s1 v3 v2 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (native_ite_true_rep _ hx_4 h_v4)
    · ite_branch hbv_4
      store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s2 e_v6 (by rw [he_v6]; rfl) h_v1 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_4 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v7 in EoCases.__eo_to_smt_type.case_1 using

theorem case_2_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDatatypeTypeRef.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_type.case_2
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  have h_ite_v5 := (show if_1_eo__24eo_5fto_5fsmt_5ftype s1 v2 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24eo_5fto_5fsmt_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v2 with ⟨hx_3, hbv_3⟩ | ⟨hx_3, hbv_3⟩
    · ite_branch hbv_3
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_true_rep _ hx_3 h_v3)
    · ite_branch hbv_3
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eTypeRef.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_3 h_v4))
  store_step with h_ite_v5 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v5 in EoCases.__eo_to_smt_type.case_2 using

theorem case_3_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_type.case_3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDtcAppType.construct s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5ftypeof_5fguard s5 v4 v7 _ _ hinv5 h64 (hG.rem hrem) h_v4 h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24smtx_5ftypeof_5fguard s6 v3 v8 _ _ hinv6 h64 (hG.rem hrem) h_v3 h_v8 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv7 hG with h_v9 in EoCases.__eo_to_smt_type.case_3 using

theorem case_4_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUSort.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_type.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eUSort.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_to_smt_type.case_4 using

theorem case_5_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_5
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_5
  pat_is_node h_v4 : x_v4 is Eo.Term.FunType by Embed.inv_Term_FunType else hinv hG in EoCases.__eo_to_smt_type.case_5
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v5 _ hinv h64 hrem h_v5 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s4 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24smtx_5ftypeof_5fguard s5 v8 v11 _ _ hinv5 h64 (hG.rem hrem) h_v8 h_v11 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24smtx_5ftypeof_5fguard s6 v7 v12 _ _ hinv6 h64 (hG.rem hrem) h_v7 h_v12 as ⟨v13, s7, hinv7, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv7 hG with h_v13 in EoCases.__eo_to_smt_type.case_5 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_6_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_6
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_6 using

theorem case_7_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_7
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_7 using

theorem case_8_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_8
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_8
  pat_destruct_lit Store.destruct_numeral_spec s1 v2 h_v2 hinv1 h64 as ⟨v5, x_v5, h_v5⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 in EoCases.__eo_to_smt_type.case_8
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_zleq s3 e_v7 (by rw [he_v7]; rfl) h_v6 h_v5 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6
  rw [← Bridge.native_zleq] at h_v7
  have h_ite_v11 := (show if_2_eo__24eo_5fto_5fsmt_5ftype s4 v7 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24eo_5fto_5fsmt_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_int_to_nat s4 e_v8 (by rw [he_v8]; rfl) h_v5 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7
      rw [← Bridge.native_int_to_nat] at h_v8
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s5 e_v9 (by rw [he_v9]; rfl) h_v8 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7 h_v8
      ite_done hinv6 hG with (native_ite_true_rep _ hx_8 h_v9)
    · ite_branch hbv_8
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v10))
  store_step with h_ite_v11 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v11 in EoCases.__eo_to_smt_type.case_8 using hn_v1 hn_v2

theorem case_9_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Char.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_9
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_9 using

theorem case_10_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_10_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_10
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_10
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fguard s4 v4 v6 _ _ hinv4 h64 (hG.rem hrem) h_v4 h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v7 in EoCases.__eo_to_smt_type.case_10 using hn_v1 hn_v2

theorem case_11_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_11_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_type.case_11 using

theorem cases_0_0_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_0 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_1 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_2 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_0 x_a0] ++ [EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0] ++ [EoCases.__eo_to_smt_type.case_1 x_a0] ++ [EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0] ++ [EoCases.__eo_to_smt_type.case_2 x_a0] ++ [EoCases.__eo_to_smt_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0] ++ [EoCases.__eo_to_smt_type.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_4 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_5 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_6 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_4 x_a0] ++ [EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [EoCases.__eo_to_smt_type.case_4 x_a0] ++ [EoCases.__eo_to_smt_type.case_5 x_a0] ++ [EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0] ++ [EoCases.__eo_to_smt_type.case_6 x_a0] ++ [EoCases.__eo_to_smt_type.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0] ++ [EoCases.__eo_to_smt_type.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_8 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_9 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_10 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_8 x_a0] ++ [EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_8 x_a0] ++ [EoCases.__eo_to_smt_type.case_9 x_a0] ++ [EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_step with case_10_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0] ++ [EoCases.__eo_to_smt_type.case_10 x_a0] ++ [EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hl_8 hl_9
  group_step with case_11_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0] ++ [EoCases.__eo_to_smt_type.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

/-- logos's `__eo_to_smt_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_type x_a0 =
      (firstSome [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_type
  unfold EoCases.__eo_to_smt_type.case_0 EoCases.__eo_to_smt_type.case_1 EoCases.__eo_to_smt_type.case_2 EoCases.__eo_to_smt_type.case_3 EoCases.__eo_to_smt_type.case_4 EoCases.__eo_to_smt_type.case_5 EoCases.__eo_to_smt_type.case_6 EoCases.__eo_to_smt_type.case_7 EoCases.__eo_to_smt_type.case_8 EoCases.__eo_to_smt_type.case_9 EoCases.__eo_to_smt_type.case_10 EoCases.__eo_to_smt_type.case_11
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  body_group_step with cases_0_0_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] ++ [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_step with cases_0_1_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] ++ [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] ++ [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] ++ [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 in EoCases.__eo_to_smt_type.case_0 EoCases.__eo_to_smt_type.case_1 EoCases.__eo_to_smt_type.case_2 EoCases.__eo_to_smt_type.case_3 EoCases.__eo_to_smt_type.case_4 EoCases.__eo_to_smt_type.case_5 EoCases.__eo_to_smt_type.case_6 EoCases.__eo_to_smt_type.case_7 EoCases.__eo_to_smt_type.case_8 EoCases.__eo_to_smt_type.case_9 EoCases.__eo_to_smt_type.case_10 EoCases.__eo_to_smt_type.case_11 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5ftype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 46#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5ftype s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_46 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_46 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_boolean_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v2 (by rw [he_v2]; exact empty_args) hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_typeof.case_0 using hn_a0

theorem case_1_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_numeral_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with Store.construct_numeral_spec s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5flit_5ftype_5fNumeral s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_typeof.case_1 using hn_a0

theorem case_2_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_rational_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with Store.construct_rational_spec s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5flit_5ftype_5fRational s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_typeof.case_2 using hn_a0

theorem case_3_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_string_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with Store.construct_string_spec s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5flit_5ftype_5fString s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_typeof.case_3 using hn_a0

theorem case_4_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit2 Store.destruct_binary_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_4
  step as ⟨e_v3, he_v3⟩
  store_step with Store.construct_binary_spec s1 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 (Store.rep_binary_okBv h_a0) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5flit_5ftype_5fBinary s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__eo_typeof.case_4 using hn_a0

theorem case_5_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_5
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a0
  pat_destruct_lit Store.destruct_string_spec s v1 h_v1 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_v1 h_v2 in EoCases.__eo_typeof.case_5
  case_done hinv1 hG with h_v2 in EoCases.__eo_typeof.case_5 using hn_a0 hn_v1 hn_v2

theorem case_6_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_6_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDatatypeType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_6
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__eo_typeof.case_6 using hn_a0

theorem case_7_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_7_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_typeof.case_7
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fDatatypeType.construct s e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fdd_5fresolve s1 v1 v2 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5ftypeof_5fdt_5fcons_5frec s2 v4 v5 v3 _ _ _ hinv2 h64 (hG.rem hrem) h_v4 h_v5 h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__eo_typeof.case_7 using hn_a0

theorem case_8_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_8_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtSel.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_8
  store_step with ih.eo__24eo_5fdd_5fresolve s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5ftypeof_5fdt_5fsel_5freturn s1 v5 v3 v4 _ _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v3 h_v4 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fDatatypeType.construct s2 e_v7 (by rw [he_v7]; rfl) h_v1 h_v2 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fFunType.construct s3 e_v8 (by rw [he_v8]; exact empty_args) hinv3 h64 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_mk_rep s4 v8 v7 _ _ hinv4 h64 h_v8 h_v7 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_mk_rep s5 v9 v6 _ _ hinv5 h64 h_v9 h_v6 as ⟨v10, s6, hinv6, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv6 hG with h_v10 in EoCases.__eo_typeof.case_8 using hn_a0

theorem case_9_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_9_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUSort.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_typeof.case_9
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_typeof.case_9 using hn_a0

theorem case_10_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_10_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUConst.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_10
  case_done hinv hG with h_v2 in EoCases.__eo_typeof.case_10 using hn_a0

theorem case_11_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_11_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_11
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_11 using hn_a0

theorem case_12_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_12_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_12
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_12
  pat_is_node h_v4 : x_v4 is Eo.Term.FunType by Embed.inv_Term_FunType else hinv hG in EoCases.__eo_typeof.case_12
  store_step with ih.eo__24eo_5ftypeof s v5 _ hinv h64 hrem h_v5 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24eo_5ftypeof_5ffun_5ftype s2 v7 v8 _ _ hinv2 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  case_done hinv3 hG with h_v9 in EoCases.__eo_typeof.case_12 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_13_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_13_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_13
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_13 using hn_a0

theorem case_14_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_14_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_14
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_14 using hn_a0

theorem case_15_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_15_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_15 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_15
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_15 using hn_a0

theorem case_16_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_16_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_16 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_16
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_16
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fFunType.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s4 v6 v5 _ _ hinv4 h64 h_v6 h_v5 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s5 v7 v4 _ _ hinv5 h64 h_v7 h_v4 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_typeof.case_16 using hn_a0 hn_v1 hn_v2

theorem case_17_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_17_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_17 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_17 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_17_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_17
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_17 using hn_a0

theorem case_18_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_18_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_18 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_18 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_18_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_18
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_18 using hn_a0

theorem case_19_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_19_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_19 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_19_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_19
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_19
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fBitVec s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_19 using hn_a0 hn_v1 hn_v2

theorem case_20_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_20_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_20 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_20 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_20_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Char.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_20
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_20 using hn_a0

theorem case_21_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_21_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_21 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_21 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_21_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_21
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_21
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fSeq s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_21 using hn_a0 hn_v1 hn_v2

theorem case_22_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_22_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_22 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_22 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_22_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_22
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_22
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fnot s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_22 using hn_a0 hn_v1 hn_v2

theorem case_23_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_23_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_23 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_23_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_23
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_23
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_23
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_23 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_24_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_24_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_24 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_24 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_24_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_24
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_24
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_24
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_24 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_25_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_25_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_25 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_25 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_25_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_25
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_25
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_25
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_3d s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_25 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_26_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_26_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_26 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_26 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_26_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_26
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fapply s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_26 using hn_a0 hn_v1 hn_v2

theorem cases_0_0_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_0 x_a0 = none ∧ EoCases.__eo_typeof.case_1 x_a0 = none ∧ EoCases.__eo_typeof.case_2 x_a0 = none ∧ EoCases.__eo_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [] ++ [EoCases.__eo_typeof.case_0 x_a0] ++ [EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [EoCases.__eo_typeof.case_0 x_a0] ++ [EoCases.__eo_typeof.case_1 x_a0] ++ [EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0] ++ [EoCases.__eo_typeof.case_2 x_a0] ++ [EoCases.__eo_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0] ++ [EoCases.__eo_typeof.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_4 x_a0 = none ∧ EoCases.__eo_typeof.case_5 x_a0 = none ∧ EoCases.__eo_typeof.case_6 x_a0 = none ∧ EoCases.__eo_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [] ++ [EoCases.__eo_typeof.case_4 x_a0] ++ [EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [EoCases.__eo_typeof.case_4 x_a0] ++ [EoCases.__eo_typeof.case_5 x_a0] ++ [EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_step with case_6_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0] ++ [EoCases.__eo_typeof.case_6 x_a0] ++ [EoCases.__eo_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hl_4 hl_5
  group_step with case_7_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0] ++ [EoCases.__eo_typeof.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_8 x_a0 = none ∧ EoCases.__eo_typeof.case_9 x_a0 = none ∧ EoCases.__eo_typeof.case_10 x_a0 = none ∧ EoCases.__eo_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [] ++ [EoCases.__eo_typeof.case_8 x_a0] ++ [EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0
  group_step with case_9_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [EoCases.__eo_typeof.case_8 x_a0] ++ [EoCases.__eo_typeof.case_9 x_a0] ++ [EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hn_a0 hl_8
  group_step with case_10_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0] ++ [EoCases.__eo_typeof.case_10 x_a0] ++ [EoCases.__eo_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hn_a0 hl_8 hl_9
  group_step with case_11_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0] ++ [EoCases.__eo_typeof.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hn_a0 hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_3_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_12 x_a0 = none ∧ EoCases.__eo_typeof.case_13 x_a0 = none ∧ EoCases.__eo_typeof.case_14 x_a0 = none ∧ EoCases.__eo_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [] ++ [EoCases.__eo_typeof.case_12 x_a0] ++ [EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using hn_a0
  group_step with case_13_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_12 x_a0] ++ [EoCases.__eo_typeof.case_13 x_a0] ++ [EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hn_a0 hl_12
  group_step with case_14_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0] ++ [EoCases.__eo_typeof.case_14 x_a0] ++ [EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_14⟩ using hn_a0 hl_12 hl_13
  group_step with case_15_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0] ++ [EoCases.__eo_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hn_a0 hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_4_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_16 x_a0 = none ∧ EoCases.__eo_typeof.case_17 x_a0 = none ∧ EoCases.__eo_typeof.case_18 x_a0 = none ∧ EoCases.__eo_typeof.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_16_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [] ++ [EoCases.__eo_typeof.case_16 x_a0] ++ [EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_16⟩ using hn_a0
  group_step with case_17_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [EoCases.__eo_typeof.case_16 x_a0] ++ [EoCases.__eo_typeof.case_17 x_a0] ++ [EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_17⟩ using hn_a0 hl_16
  group_step with case_18_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0] ++ [EoCases.__eo_typeof.case_18 x_a0] ++ [EoCases.__eo_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_18⟩ using hn_a0 hl_16 hl_17
  group_step with case_19_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0] ++ [EoCases.__eo_typeof.case_19 x_a0] ++ [] from rfl)
    otherwise ⟨hl_19⟩ using hn_a0 hl_16 hl_17 hl_18
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19⟩

theorem cases_0_5_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_5_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_20 x_a0 = none ∧ EoCases.__eo_typeof.case_21 x_a0 = none ∧ EoCases.__eo_typeof.case_22 x_a0 = none ∧ EoCases.__eo_typeof.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_5_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_20_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [] ++ [EoCases.__eo_typeof.case_20 x_a0] ++ [EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_20⟩ using hn_a0
  group_step with case_21_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [EoCases.__eo_typeof.case_20 x_a0] ++ [EoCases.__eo_typeof.case_21 x_a0] ++ [EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_21⟩ using hn_a0 hl_20
  group_step with case_22_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0] ++ [EoCases.__eo_typeof.case_22 x_a0] ++ [EoCases.__eo_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_22⟩ using hn_a0 hl_20 hl_21
  group_step with case_23_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0] ++ [EoCases.__eo_typeof.case_23 x_a0] ++ [] from rfl)
    otherwise ⟨hl_23⟩ using hn_a0 hl_20 hl_21 hl_22
  group_none hinv4 hG with ⟨hl_20, hl_21, hl_22, hl_23⟩

theorem cases_0_6_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_6_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_24 x_a0 = none ∧ EoCases.__eo_typeof.case_25 x_a0 = none ∧ EoCases.__eo_typeof.case_26 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_6_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_24_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [] ++ [EoCases.__eo_typeof.case_24 x_a0] ++ [EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] from rfl)
    otherwise ⟨hl_24⟩ using hn_a0
  group_step with case_25_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [EoCases.__eo_typeof.case_24 x_a0] ++ [EoCases.__eo_typeof.case_25 x_a0] ++ [EoCases.__eo_typeof.case_26 x_a0] from rfl)
    otherwise ⟨hl_25⟩ using hn_a0 hl_24
  group_step with case_26_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0] ++ [EoCases.__eo_typeof.case_26 x_a0] ++ [] from rfl)
    otherwise ⟨hl_26⟩ using hn_a0 hl_24 hl_25
  group_none hinv3 hG with ⟨hl_24, hl_25, hl_26⟩

theorem cases_1_0_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_0_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_0 x_a0 = none ∧ EoCases.__eo_typeof.case_1 x_a0 = none ∧ EoCases.__eo_typeof.case_2 x_a0 = none ∧ EoCases.__eo_typeof.case_3 x_a0 = none ∧ EoCases.__eo_typeof.case_4 x_a0 = none ∧ EoCases.__eo_typeof.case_5 x_a0 = none ∧ EoCases.__eo_typeof.case_6 x_a0 = none ∧ EoCases.__eo_typeof.case_7 x_a0 = none ∧ EoCases.__eo_typeof.case_8 x_a0 = none ∧ EoCases.__eo_typeof.case_9 x_a0 = none ∧ EoCases.__eo_typeof.case_10 x_a0 = none ∧ EoCases.__eo_typeof.case_11 x_a0 = none ∧ EoCases.__eo_typeof.case_12 x_a0 = none ∧ EoCases.__eo_typeof.case_13 x_a0 = none ∧ EoCases.__eo_typeof.case_14 x_a0 = none ∧ EoCases.__eo_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_0_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [] ++ [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] ++ [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  group_step with cases_0_1_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] ++ [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] ++ [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  group_step with cases_0_2_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] ++ [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] ++ [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_step with cases_0_3_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] ++ [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_1_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_16 x_a0 = none ∧ EoCases.__eo_typeof.case_17 x_a0 = none ∧ EoCases.__eo_typeof.case_18 x_a0 = none ∧ EoCases.__eo_typeof.case_19 x_a0 = none ∧ EoCases.__eo_typeof.case_20 x_a0 = none ∧ EoCases.__eo_typeof.case_21 x_a0 = none ∧ EoCases.__eo_typeof.case_22 x_a0 = none ∧ EoCases.__eo_typeof.case_23 x_a0 = none ∧ EoCases.__eo_typeof.case_24 x_a0 = none ∧ EoCases.__eo_typeof.case_25 x_a0 = none ∧ EoCases.__eo_typeof.case_26 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_4_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [] ++ [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] ++ [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19⟩ using hn_a0
  group_step with cases_0_5_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] ++ [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] ++ [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] from rfl)
    otherwise ⟨hl_20, hl_21, hl_22, hl_23⟩ using hn_a0 hl_16 hl_17 hl_18 hl_19
  group_step with cases_0_6_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] ++ [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] ++ [] from rfl)
    otherwise ⟨hl_24, hl_25, hl_26⟩ using hn_a0 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23
  group_none hinv3 hG with ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26⟩

/-- logos's `__eo_typeof` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof
  unfold EoCases.__eo_typeof.case_0 EoCases.__eo_typeof.case_1 EoCases.__eo_typeof.case_2 EoCases.__eo_typeof.case_3 EoCases.__eo_typeof.case_4 EoCases.__eo_typeof.case_5 EoCases.__eo_typeof.case_6 EoCases.__eo_typeof.case_7 EoCases.__eo_typeof.case_8 EoCases.__eo_typeof.case_9 EoCases.__eo_typeof.case_10 EoCases.__eo_typeof.case_11 EoCases.__eo_typeof.case_12 EoCases.__eo_typeof.case_13 EoCases.__eo_typeof.case_14 EoCases.__eo_typeof.case_15 EoCases.__eo_typeof.case_16 EoCases.__eo_typeof.case_17 EoCases.__eo_typeof.case_18 EoCases.__eo_typeof.case_19 EoCases.__eo_typeof.case_20 EoCases.__eo_typeof.case_21 EoCases.__eo_typeof.case_22 EoCases.__eo_typeof.case_23 EoCases.__eo_typeof.case_24 EoCases.__eo_typeof.case_25 EoCases.__eo_typeof.case_26
  logos_eq

theorem body_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_1_0_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [] ++ [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] ++ [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using hn_a0
  body_group_step with cases_1_1_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] ++ [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] ++ [] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  body_stuck hinv2 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 in EoCases.__eo_typeof.case_0 EoCases.__eo_typeof.case_1 EoCases.__eo_typeof.case_2 EoCases.__eo_typeof.case_3 EoCases.__eo_typeof.case_4 EoCases.__eo_typeof.case_5 EoCases.__eo_typeof.case_6 EoCases.__eo_typeof.case_7 EoCases.__eo_typeof.case_8 EoCases.__eo_typeof.case_9 EoCases.__eo_typeof.case_10 EoCases.__eo_typeof.case_11 EoCases.__eo_typeof.case_12 EoCases.__eo_typeof.case_13 EoCases.__eo_typeof.case_14 EoCases.__eo_typeof.case_15 EoCases.__eo_typeof.case_16 EoCases.__eo_typeof.case_17 EoCases.__eo_typeof.case_18 EoCases.__eo_typeof.case_19 EoCases.__eo_typeof.case_20 EoCases.__eo_typeof.case_21 EoCases.__eo_typeof.case_22 EoCases.__eo_typeof.case_23 EoCases.__eo_typeof.case_24 EoCases.__eo_typeof.case_25 EoCases.__eo_typeof.case_26

theorem eo__24eo_5ftypeof_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof
  apply WP.dspec_mono (Store.framed_type_cached s hinv hrem h64 cache.TypeCacheKind.Eunoia a0
    (fun s1 => body_eo__24eo_5ftypeof s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_4294967296 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_4294967296 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__eo_typeof_eq.case_0
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_typeof_eq.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_3d.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_eq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_eq.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_eq
  unfold EoCases.__eo_typeof_eq.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_3d.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_3d_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_eq.case_0

theorem eo__24eo_5ftypeof_5f_3d_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_3d.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_3d
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_3d s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_3d_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fBitVec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fBitVec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_BitVec.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_BitVec.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fBitVec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof_BitVec.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof_BitVec.case_0 using hn_a0

/-- logos's `__eo_typeof_BitVec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fBitVec.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_BitVec x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_BitVec.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_BitVec
  unfold EoCases.__eo_typeof_BitVec.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fBitVec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fBitVec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_BitVec x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fBitVec.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fBitVec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fBitVec_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_BitVec.case_0

theorem eo__24eo_5ftypeof_5fBitVec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fBitVec.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fBitVec
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fBitVec s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_BitVec x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fBitVec_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fSeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fSeq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_Seq.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_Seq.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fSeq
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof_Seq.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof_Seq.case_0 using hn_a0

/-- logos's `__eo_typeof_Seq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fSeq.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_Seq x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_Seq.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_Seq
  unfold EoCases.__eo_typeof_Seq.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fSeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fSeq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_Seq x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fSeq.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fSeq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fSeq_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_Seq.case_0

theorem eo__24eo_5ftypeof_5fSeq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fSeq.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fSeq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fSeq s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_Seq x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fSeq_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_and.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_and.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fand
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof_and.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof_and.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof_and.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof_and` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fand.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_and x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_and.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_and
  unfold EoCases.__eo_typeof_and.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5fand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_and x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fand.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5fand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fand_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_and.case_0

theorem eo__24eo_5ftypeof_5fand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fand.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5fand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fand s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_and x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fand_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_apply.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_apply.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_apply.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof_apply.case_0
  pat_is_node h_v4 : x_v4 is Eo.Term.FunType by Embed.inv_Term_FunType else hinv hG in EoCases.__eo_typeof_apply.case_0
  have h_req_v7 := (show requires_0_eo__24eo_5ftypeof_5fapply s v5 a1 v2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5fapply
    have hG := Store.Grows.refl s
    req_same v5 a1 with h_v5 h_a1 using hinv hG
    req_stuck h_v5 as hq_v5 using hinv hG
    req_done hinv hG with h_v2 using hq_v5)
  store_step with h_req_v7 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  case_done hinv1 hG with h_v7 in EoCases.__eo_typeof_apply.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_apply.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_apply.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_apply.case_1
  have h_req_v3 := (show requires_1_eo__24eo_5ftypeof_5fapply s v1 a1 v2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5ftypeof_5fapply
    have hG := Store.Grows.refl s
    req_same v1 a1 with h_v1 h_a1 using hinv hG
    req_stuck h_v1 as hq_v1 using hinv hG
    req_done hinv hG with h_v2 using hq_v1)
  store_step with h_req_v3 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__eo_typeof_apply.case_1 using hn_a0 hn_a1

/-- logos's `__eo_typeof_apply` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fapply.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_apply x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_apply.case_0 x_a0 x_a1, EoCases.__eo_typeof_apply.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_apply
  unfold EoCases.__eo_typeof_apply.case_0 EoCases.__eo_typeof_apply.case_1
  logos_eq

theorem body_eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_apply x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fapply.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fapply_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24eo_5ftypeof_5fapply_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__eo_typeof_apply.case_0 EoCases.__eo_typeof_apply.case_1

theorem eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fapply.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5fapply
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fapply s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_apply x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fapply_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = some (__eo_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_dt_cons_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_dt_cons_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s1 a2 h_a2 hinv1 h64 storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 in EoCases.__eo_typeof_dt_cons_rec.case_0
  case_done hinv2 hG with h_a0 in EoCases.__eo_typeof_dt_cons_rec.case_0 using hn_a0

theorem case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = some (__eo_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_dt_cons_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_typeof_dt_cons_rec.case_1
  pat_native_zero Store.native_pattern_nat_zero_spec s a2 h_a2 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__eo_typeof_dt_cons_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fedt_2esum.construct s1 e_v7 (by rw [he_v7]; rfl) h_v5 h_v2 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  store_step with Store.native_nat_zero_spec s2 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fdt_5fcons_5frec s3 a0 v7 v8 _ _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fDtcAppType.construct s4 e_v10 (by rw [he_v10]; rfl) h_v4 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__eo_typeof_dt_cons_rec.case_1 using hn_a0

theorem case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = some (__eo_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_dt_cons_rec.case_2
  pat_destruct_lit Store.native_pattern_succ_spec s a2 h_a2 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__eo_typeof_dt_cons_rec.case_2
  case_again hinv1 hG with h_a0 h_v2 h_v4 in EoCases.__eo_typeof_dt_cons_rec.case_2 using hn_a0

/-- logos's `__eo_typeof_dt_cons_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fdt_5fcons_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_typeof_dt_cons_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2, EoCases.__eo_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2, EoCases.__eo_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_dt_cons_rec
  unfold EoCases.__eo_typeof_dt_cons_rec.case_0 EoCases.__eo_typeof_dt_cons_rec.case_1 EoCases.__eo_typeof_dt_cons_rec.case_2
  logos_eq

theorem step_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24eo_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __eo_typeof_dt_cons_rec x_a0 x_a1 x_a2 = __eo_typeof_dt_cons_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fdt_5fcons_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24eo_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  round_step with case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0
  round_step with case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hc0
  round_step with case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hc0 hc1 hc2 in EoCases.__eo_typeof_dt_cons_rec.case_0 EoCases.__eo_typeof_dt_cons_rec.case_1 EoCases.__eo_typeof_dt_cons_rec.case_2

theorem body_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24eo_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24eo_5ftypeof_5fdt_5fcons_5frec body_eo__24eo_5ftypeof_5fdt_5fcons_5frec_loop
  step with step_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24eo_5ftypeof_5fdt_5fcons_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fdt_5fcons_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5ftypeof_5fdt_5fcons_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 53#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24eo_5ftypeof_5fdt_5fcons_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_typeof_dt_cons_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_53 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_53 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_typeof_dt_sel_return.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_typeof_dt_sel_return.case_0 x_a0 x_a1 x_a2 = some (__eo_typeof_dt_sel_return y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_typeof_dt_sel_return.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_dt_sel_return.case_0
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_typeof_dt_sel_return.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s a1 h_a1 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__eo_typeof_dt_sel_return.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s1 a2 h_a2 hinv1 h64 storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__eo_typeof_dt_sel_return.case_0
  case_done hinv2 hG with h_v4 in EoCases.__eo_typeof_dt_sel_return.case_0 using

theorem case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_typeof_dt_sel_return.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_typeof_dt_sel_return.case_1 x_a0 x_a1 x_a2 = some (__eo_typeof_dt_sel_return y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_typeof_dt_sel_return.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_dt_sel_return.case_1
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_typeof_dt_sel_return.case_1
  pat_native_zero Store.native_pattern_nat_zero_spec s a1 h_a1 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__eo_typeof_dt_sel_return.case_1
  pat_destruct_lit Store.native_pattern_succ_spec s1 a2 h_a2 hinv1 h64 as ⟨v8, x_v8, h_v8⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__eo_typeof_dt_sel_return.case_1
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fedt_2esum.construct s2 e_v9 (by rw [he_v9]; rfl) h_v5 h_v2 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v8
  store_step with Store.native_nat_zero_spec s3 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v8 h_v9
  case_again hinv4 hG with h_v9 h_v10 h_v8 in EoCases.__eo_typeof_dt_sel_return.case_1 using

theorem case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_typeof_dt_sel_return.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_typeof_dt_sel_return.case_2 x_a0 x_a1 x_a2 = some (__eo_typeof_dt_sel_return y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_typeof_dt_sel_return.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_dt_sel_return.case_2
  pat_destruct_lit Store.native_pattern_succ_spec s a1 h_a1 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__eo_typeof_dt_sel_return.case_2
  case_again hinv1 hG with h_v2 h_v4 h_a2 in EoCases.__eo_typeof_dt_sel_return.case_2 using

/-- logos's `__eo_typeof_dt_sel_return` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fdt_5fsel_5freturn.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_typeof_dt_sel_return x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_typeof_dt_sel_return.case_0 x_a0 x_a1 x_a2, EoCases.__eo_typeof_dt_sel_return.case_1 x_a0 x_a1 x_a2, EoCases.__eo_typeof_dt_sel_return.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_dt_sel_return
  unfold EoCases.__eo_typeof_dt_sel_return.case_0 EoCases.__eo_typeof_dt_sel_return.case_1 EoCases.__eo_typeof_dt_sel_return.case_2
  logos_eq

theorem step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_typeof_dt_sel_return x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __eo_typeof_dt_sel_return x_a0 x_a1 x_a2 = __eo_typeof_dt_sel_return y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fdt_5fsel_5freturn.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  round_step with case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using
  round_step with case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0
  round_step with case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1
  round_stuck hinv4 hG using hc0 hc1 hc2 in EoCases.__eo_typeof_dt_sel_return.case_0 EoCases.__eo_typeof_dt_sel_return.case_1 EoCases.__eo_typeof_dt_sel_return.case_2

theorem body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_dt_sel_return x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_dt_sel_return x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_loop
  step with step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fdt_5fsel_5freturn.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5ftypeof_5fdt_5fsel_5freturn
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 54#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_typeof_dt_sel_return x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_54 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_54 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5ffun_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5ffun_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_fun_type.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_fun_type.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5ffun_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof_fun_type.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof_fun_type.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof_fun_type.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof_fun_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5ffun_5ftype.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_fun_type x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_fun_type.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_fun_type
  unfold EoCases.__eo_typeof_fun_type.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5ffun_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5ffun_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_fun_type x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5ffun_5ftype.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5ffun_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5ffun_5ftype_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_fun_type.case_0

theorem eo__24eo_5ftypeof_5ffun_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5ffun_5ftype.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5ffun_5ftype
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5ffun_5ftype s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_fun_type x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5ffun_5ftype_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fnot_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_not.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_not.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fnot
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof_not.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof_not.case_0 using hn_a0

/-- logos's `__eo_typeof_not` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fnot.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_not x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_not.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_not
  unfold EoCases.__eo_typeof_not.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fnot_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_not x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fnot.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fnot
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fnot_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_not.case_0

theorem eo__24eo_5ftypeof_5fnot_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fnot.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fnot
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fnot s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_not x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fnot_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_symm.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_symm.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fsymm
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_symm.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_symm.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_symm.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v2 _ _ hinv2 h64 h_v7 h_v2 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__mk_symm.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_symm.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_symm.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fsymm
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_symm.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_symm.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__mk_symm.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_symm.case_1
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__mk_symm.case_1
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_not.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s4 v12 v6 _ _ hinv4 h64 h_v12 h_v6 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s5 v13 v9 _ _ hinv5 h64 h_v13 h_v9 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s6 v11 v14 _ _ hinv6 h64 h_v11 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  case_done hinv7 hG with h_v15 in EoCases.__mk_symm.case_1 using hn_a0 hn_v1 hn_v2 hn_v5 hn_v6 hn_v8 hn_v9

/-- logos's `__mk_symm` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fsymm.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __mk_symm x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_symm.case_0 x_a0, EoCases.__mk_symm.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __mk_symm
  unfold EoCases.__mk_symm.case_0 EoCases.__mk_symm.case_1
  logos_eq

theorem body_eo__24mk_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24mk_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_symm x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fsymm.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24mk_5fsymm
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24mk_5fsymm_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24mk_5fsymm_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__mk_symm.case_0 EoCases.__mk_symm.case_1

theorem eo__24mk_5fsymm_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fsymm.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24mk_5fsymm
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fsymm s1 a0) (fun s' t => Represents.rep s' t (__mk_symm x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fsymm_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_trans.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_trans.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5ftrans
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_trans.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_trans.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_trans.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_trans.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_trans.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_trans.case_0
  have h_req_v15 := (show requires_0_eo__24mk_5ftrans s2 a1 v12 a0 v9 v2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24mk_5ftrans
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same a1 v12 with h_a1 h_v12 using hinv2 hG
    req_stuck h_a1 as hq_a1 using hinv2 hG
    store_step with ih.eo__24mk_5ftrans s2 a0 v9 v2 _ _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v9 h_v2 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
    req_done hinv3 hG with h_v14 using hq_a1)
  store_step with h_req_v15 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  case_done hinv4 hG with h_v15 in EoCases.__mk_trans.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24mk_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_trans.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_trans.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5ftrans
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_trans.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__mk_trans.case_1 using hn_a0 hn_a1 hn_a2

/-- logos's `__mk_trans` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5ftrans.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_trans x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_trans.case_0 x_a0 x_a1 x_a2, EoCases.__mk_trans.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_trans
  unfold EoCases.__mk_trans.case_0 EoCases.__mk_trans.case_1
  logos_eq

theorem body_eo__24mk_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_trans x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5ftrans.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5ftrans
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5ftrans_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24mk_5ftrans_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_trans.case_0 EoCases.__mk_trans.case_1

theorem eo__24mk_5ftrans_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5ftrans.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5ftrans
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 58#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5ftrans s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_trans x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_58 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_58 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5ftrans_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdd_5fhas_5fdt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_has_dt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_has_dt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdd_5fhas_5fdt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_dd_has_dt.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_streq] at h_v4
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_or s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  rw [← Bridge.native_or] at h_v6
  case_done hinv3 hG with h_v6 in EoCases.__smtx_dd_has_dt.case_0 using

theorem case_1_eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdd_5fhas_5fdt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_has_dt.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_has_dt.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdd_5fhas_5fdt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dd_has_dt.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dd_has_dt.case_1 using

/-- logos's `__smtx_dd_has_dt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdd_5fhas_5fdt.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dd_has_dt x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dd_has_dt.case_0 x_a0 x_a1, EoCases.__smtx_dd_has_dt.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dd_has_dt
  unfold EoCases.__smtx_dd_has_dt.case_0 EoCases.__smtx_dd_has_dt.case_1
  logos_eq

theorem body_eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdd_5fhas_5fdt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dd_has_dt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdd_5fhas_5fdt.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdd_5fhas_5fdt
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdd_5fhas_5fdt_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdd_5fhas_5fdt_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dd_has_dt.case_0 EoCases.__smtx_dd_has_dt.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdd_5fhas_5fdt.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdd_5fhas_5fdt
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 59#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdd_5fhas_5fdt s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dd_has_dt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_59 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_59 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdd_5fhas_5fdt_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_lookup.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_lookup.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdd_5flookup
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_dd_lookup.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_streq] at h_v4
  have h_ite_v6 := (show if_0_eo__24smtx_5fdd_5flookup s1 v4 v2 a0 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5fdd_5flookup
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_v2)
    · ite_branch hbv_5
      store_step with ih.eo__24smtx_5fdd_5flookup s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__smtx_dd_lookup.case_0 using

theorem case_1_eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_lookup.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_lookup.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdd_5flookup
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dd_lookup.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dd_lookup.case_1 using

/-- logos's `__smtx_dd_lookup` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdd_5flookup.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dd_lookup x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dd_lookup.case_0 x_a0 x_a1, EoCases.__smtx_dd_lookup.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_dd_lookup
  unfold EoCases.__smtx_dd_lookup.case_0 EoCases.__smtx_dd_lookup.case_1
  logos_eq

theorem body_eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dd_lookup x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdd_5flookup.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdd_5flookup
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdd_5flookup_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdd_5flookup_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dd_lookup.case_0 EoCases.__smtx_dd_lookup.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdd_5flookup.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdd_5flookup
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 60#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdd_5flookup s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dd_lookup x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_60 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_60 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdd_5flookup_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdecl_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_inhabited.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_inhabited.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdecl_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_decl_inhabited.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_streq] at h_v4
  have h_ite_v7 := (show if_0_eo__24smtx_5fdecl_5finhabited s1 v4 v2 v3 a0 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5fdecl_5finhabited
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      store_step with ih.eo__24smtx_5fdt_5finhabited s1 v2 v3 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      store_step with ih.eo__24smtx_5fdecl_5finhabited s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v7 in EoCases.__smtx_decl_inhabited.case_0 using

theorem case_1_eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdecl_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_inhabited.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_inhabited.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdecl_5finhabited
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_decl_inhabited.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_decl_inhabited.case_1 using

/-- logos's `__smtx_decl_inhabited` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdecl_5finhabited.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_decl_inhabited x_a0 x_a1 =
      (firstSome [EoCases.__smtx_decl_inhabited.case_0 x_a0 x_a1, EoCases.__smtx_decl_inhabited.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_decl_inhabited
  unfold EoCases.__smtx_decl_inhabited.case_0 EoCases.__smtx_decl_inhabited.case_1
  logos_eq

theorem body_eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdecl_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_decl_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdecl_5finhabited.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdecl_5finhabited
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdecl_5finhabited_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdecl_5finhabited_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_decl_inhabited.case_0 EoCases.__smtx_decl_inhabited.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdecl_5finhabited.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdecl_5finhabited
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 61#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdecl_5finhabited s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_decl_inhabited x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_61 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_61 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdecl_5finhabited_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdecl_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_wf_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_wf_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdecl_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_decl_wf_rec.case_0
  store_step with ih.eo__24smtx_5fdt_5fwf_5frec s a0 v2 _ _ hinv h64 hrem h_a0 h_v2 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 h_a0 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5finhabited_5ftype s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5fdecl_5fwf_5frec s3 a0 v3 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s4 v1 v3 _ _ hinv4 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.native_spec_not s5 e_v9 (by rw [he_v9]; rfl) h_v8 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  rw [← Bridge.native_not] at h_v9
  step as ⟨e_v10, he_v10⟩
  store_step with Store.native_spec_and s6 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  rw [← Bridge.native_and] at h_v10
  step as ⟨e_v11, he_v11⟩
  store_step with Store.native_spec_and s7 e_v11 (by rw [he_v11]; rfl) h_v6 h_v10 hinv7 h64 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  rw [← Bridge.native_and] at h_v11
  step as ⟨e_v12, he_v12⟩
  store_step with Store.native_spec_and s8 e_v12 (by rw [he_v12]; rfl) h_v4 h_v11 hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  rw [← Bridge.native_and] at h_v12
  case_done hinv9 hG with h_v12 in EoCases.__smtx_decl_wf_rec.case_0 using

theorem case_1_eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdecl_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_wf_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_wf_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdecl_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_decl_wf_rec.case_1
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_decl_wf_rec.case_1 using

/-- logos's `__smtx_decl_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdecl_5fwf_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_decl_wf_rec x_a0 x_a1 =
      (firstSome [EoCases.__smtx_decl_wf_rec.case_0 x_a0 x_a1, EoCases.__smtx_decl_wf_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_decl_wf_rec
  unfold EoCases.__smtx_decl_wf_rec.case_0 EoCases.__smtx_decl_wf_rec.case_1
  logos_eq

theorem body_eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdecl_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_decl_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdecl_5fwf_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdecl_5fwf_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdecl_5fwf_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdecl_5fwf_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_decl_wf_rec.case_0 EoCases.__smtx_decl_wf_rec.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdecl_5fwf_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdecl_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 62#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdecl_5fwf_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_decl_wf_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_62 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_62 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdecl_5fwf_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_inhabited.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_inhabited.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_inhabited.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__smtx_dt_cons_inhabited.case_0
  store_step with ih.eo__24smtx_5fdecl_5finhabited s v4 a1 _ _ hinv h64 hrem h_v4 h_a1 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24smtx_5fdt_5fcons_5finhabited s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_and s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  rw [← Bridge.native_and] at h_v7
  case_done hinv3 hG with h_v7 in EoCases.__smtx_dt_cons_inhabited.case_0 using

theorem case_1_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_inhabited.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_inhabited.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_inhabited.case_1
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5fcons_5finhabited s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_cons_inhabited.case_1 using

theorem case_2_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_inhabited.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_inhabited.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_cons_inhabited.case_2
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_cons_inhabited.case_2 using

/-- logos's `__smtx_dt_cons_inhabited` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fcons_5finhabited.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_cons_inhabited x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_cons_inhabited.case_0 x_a0 x_a1, EoCases.__smtx_dt_cons_inhabited.case_1 x_a0 x_a1, EoCases.__smtx_dt_cons_inhabited.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_cons_inhabited
  unfold EoCases.__smtx_dt_cons_inhabited.case_0 EoCases.__smtx_dt_cons_inhabited.case_1 EoCases.__smtx_dt_cons_inhabited.case_2
  logos_eq

theorem body_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_cons_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fcons_5finhabited.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fcons_5finhabited_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fcons_5finhabited_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5fdt_5fcons_5finhabited_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_dt_cons_inhabited.case_0 EoCases.__smtx_dt_cons_inhabited.case_1 EoCases.__smtx_dt_cons_inhabited.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fcons_5finhabited.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fcons_5finhabited
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 63#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fcons_5finhabited s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_cons_inhabited x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_63 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_63 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fcons_5finhabited_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_wf_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_wf_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_wf_rec.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__smtx_dt_cons_wf_rec.case_0
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s v4 a0 _ _ hinv h64 hrem h_v4 h_a0 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24smtx_5fdt_5fcons_5fwf_5frec s1 a0 v2 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_and s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  rw [← Bridge.native_and] at h_v7
  case_done hinv3 hG with h_v7 in EoCases.__smtx_dt_cons_wf_rec.case_0 using

theorem case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_wf_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_wf_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_wf_rec.case_1
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  store_step with ih.eo__24smtx_5fdt_5fcons_5fwf_5frec s3 a0 v2 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_and s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  rw [← Bridge.native_and] at h_v7
  case_done hinv5 hG with h_v7 in EoCases.__smtx_dt_cons_wf_rec.case_1 using

theorem case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_wf_rec.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_wf_rec.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_cons_wf_rec.case_2
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_cons_wf_rec.case_2 using

/-- logos's `__smtx_dt_cons_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fcons_5fwf_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_cons_wf_rec x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_cons_wf_rec.case_0 x_a0 x_a1, EoCases.__smtx_dt_cons_wf_rec.case_1 x_a0 x_a1, EoCases.__smtx_dt_cons_wf_rec.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_cons_wf_rec
  unfold EoCases.__smtx_dt_cons_wf_rec.case_0 EoCases.__smtx_dt_cons_wf_rec.case_1 EoCases.__smtx_dt_cons_wf_rec.case_2
  logos_eq

theorem body_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_cons_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fcons_5fwf_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_dt_cons_wf_rec.case_0 EoCases.__smtx_dt_cons_wf_rec.case_1 EoCases.__smtx_dt_cons_wf_rec.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fcons_5fwf_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fcons_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 64#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fcons_5fwf_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_cons_wf_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_64 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_64 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_inhabited.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_inhabited.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_inhabited.case_0
  store_step with ih.eo__24smtx_5fdt_5fcons_5finhabited s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5finhabited s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_or s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_or] at h_v5
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_inhabited.case_0 using

theorem case_1_eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_inhabited.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_inhabited.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5finhabited
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_inhabited.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_inhabited.case_1 using

/-- logos's `__smtx_dt_inhabited` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5finhabited.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_inhabited x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_inhabited.case_0 x_a0 x_a1, EoCases.__smtx_dt_inhabited.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_inhabited
  unfold EoCases.__smtx_dt_inhabited.case_0 EoCases.__smtx_dt_inhabited.case_1
  logos_eq

theorem body_eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5finhabited.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5finhabited
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5finhabited_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5finhabited_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dt_inhabited.case_0 EoCases.__smtx_dt_inhabited.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5finhabited.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5finhabited
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 65#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5finhabited s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_inhabited x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_65 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_65 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5finhabited_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_resolve.case_0
  store_step with ih.eo__24smtx_5fdtc_5fresolve s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_resolve.case_0 using

theorem case_1_eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_resolve.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_resolve.case_1 using

/-- logos's `__smtx_dt_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_resolve x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_resolve.case_0 x_a0 x_a1, EoCases.__smtx_dt_resolve.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_dt_resolve
  unfold EoCases.__smtx_dt_resolve.case_0 EoCases.__smtx_dt_resolve.case_1
  logos_eq

theorem body_eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dt_resolve.case_0 EoCases.__smtx_dt_resolve.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 66#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_66 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_66 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_wf_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_wf_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_wf_rec.case_0
  store_step with ih.eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 v1 _ _ hinv h64 hrem h_a0 h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5fwf_5frec s1 a0 v2 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_wf_rec.case_0 using

theorem case_1_eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_wf_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_wf_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_wf_rec.case_1
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_wf_rec.case_1 using

/-- logos's `__smtx_dt_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fwf_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_wf_rec x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_wf_rec.case_0 x_a0 x_a1, EoCases.__smtx_dt_wf_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_wf_rec
  unfold EoCases.__smtx_dt_wf_rec.case_0 EoCases.__smtx_dt_wf_rec.case_1
  logos_eq

theorem body_eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fwf_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fwf_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fwf_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fwf_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dt_wf_rec.case_0 EoCases.__smtx_dt_wf_rec.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fwf_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 67#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fwf_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_wf_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_67 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_67 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fwf_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dtc_resolve.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__smtx_dtc_resolve.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24smtx_5fdtc_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2econs.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__smtx_dtc_resolve.case_0 using

theorem case_1_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dtc_resolve.case_1
  store_step with ih.eo__24smtx_5fdtc_5fresolve s v2 a1 _ _ hinv h64 hrem h_v2 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2econs.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_dtc_resolve.case_1 using

theorem case_2_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_resolve.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_resolve.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dtc_resolve.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dtc_resolve.case_2 using

/-- logos's `__smtx_dtc_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdtc_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dtc_resolve x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dtc_resolve.case_0 x_a0 x_a1, EoCases.__smtx_dtc_resolve.case_1 x_a0 x_a1, EoCases.__smtx_dtc_resolve.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_dtc_resolve
  unfold EoCases.__smtx_dtc_resolve.case_0 EoCases.__smtx_dtc_resolve.case_1 EoCases.__smtx_dtc_resolve.case_2
  logos_eq

theorem body_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dtc_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdtc_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdtc_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdtc_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5fdtc_5fresolve_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_dtc_resolve.case_0 EoCases.__smtx_dtc_resolve.case_1 EoCases.__smtx_dtc_resolve.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdtc_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdtc_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 68#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdtc_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dtc_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_68 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_68 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdtc_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_0 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_inhabited_type.case_0
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_inhabited_type.case_0 using

theorem case_1_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_1 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_1
  case_again hinv hG with h_v2 in EoCases.__smtx_inhabited_type.case_1 using

theorem case_2_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_2 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_2
  store_step with ih.eo__24smtx_5fdecl_5finhabited s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_inhabited_type.case_2 using

theorem case_3_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_3 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_3
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_inhabited_type.case_3 using

theorem case_4_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_4 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_4
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_inhabited_type.case_4 using

theorem case_5_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_5 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_inhabited_type.case_5 using

theorem cases_0_0_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] d = __smtx_inhabited_type y0
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_0 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_1 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_2 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  group_round_step with case_0_eo__24smtx_5finhabited_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [] ++ [EoCases.__smtx_inhabited_type.case_0 x_a0] ++ [EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_round_step with case_1_eo__24smtx_5finhabited_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0] ++ [EoCases.__smtx_inhabited_type.case_1 x_a0] ++ [EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_round_step with case_2_eo__24smtx_5finhabited_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0] ++ [EoCases.__smtx_inhabited_type.case_2 x_a0] ++ [EoCases.__smtx_inhabited_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_round_step with case_3_eo__24smtx_5finhabited_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0] ++ [EoCases.__smtx_inhabited_type.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] d = __smtx_inhabited_type y0
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_4 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  group_round_step with case_4_eo__24smtx_5finhabited_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [] ++ [EoCases.__smtx_inhabited_type.case_4 x_a0] ++ [EoCases.__smtx_inhabited_type.case_5 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_round_step with case_5_eo__24smtx_5finhabited_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [EoCases.__smtx_inhabited_type.case_4 x_a0] ++ [EoCases.__smtx_inhabited_type.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__smtx_inhabited_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5finhabited_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_inhabited_type x_a0 =
      (firstSome [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0, EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_inhabited_type
  unfold EoCases.__smtx_inhabited_type.case_0 EoCases.__smtx_inhabited_type.case_1 EoCases.__smtx_inhabited_type.case_2 EoCases.__smtx_inhabited_type.case_3 EoCases.__smtx_inhabited_type.case_4 EoCases.__smtx_inhabited_type.case_5
  logos_eq

theorem step_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__smtx_inhabited_type x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __smtx_inhabited_type x_a0 = __smtx_inhabited_type y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5finhabited_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  body_group_round_step with cases_0_0_eo__24smtx_5finhabited_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 hbud
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0, EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [] ++ [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] ++ [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_round_step with cases_0_1_eo__24smtx_5finhabited_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 hbud
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0, EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] ++ [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hl_0 hl_1 hl_2 hl_3
  round_stuck hinv3 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__smtx_inhabited_type.case_0 EoCases.__smtx_inhabited_type.case_1 EoCases.__smtx_inhabited_type.case_2 EoCases.__smtx_inhabited_type.case_3 EoCases.__smtx_inhabited_type.case_4 EoCases.__smtx_inhabited_type.case_5 splitting x_a0

theorem body_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_inhabited_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_inhabited_type x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24smtx_5finhabited_5ftype body_eo__24smtx_5finhabited_5ftype_loop
  step with step_eo__24smtx_5finhabited_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, hnext, hrep0, heq⟩ := hr
      simp only
      have hlen : next.length = 1 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      have hrec := ihl s1.budget (by omega) b0 s1 y0 le_rfl hinv1 (hg1.rem hrem)  hrep0
      unfold body_eo__24smtx_5finhabited_5ftype at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5finhabited_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5finhabited_5ftype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 69#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5finhabited_5ftype s1 a0) (fun s' t => Represents.rep s' t (__smtx_inhabited_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_69 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_69 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5finhabited_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fret_5ftypeof_5fsel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_0_eo__24smtx_5fret_5ftypeof_5fsel s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fret_5ftypeof_5fsel
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5fdd_5flookup s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  store_step with ih.eo__24smtx_5fdt_5fresolve s1 v0 a1 _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel_5frec s2 v1 a2 a3 _ _ _ hinv2 h64 (hG.rem hrem) h_v1 h_a2 h_a3 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__smtx_ret_typeof_sel.case_0 using

/-- logos's `__smtx_ret_typeof_sel` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fret_5ftypeof_5fsel.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __smtx_ret_typeof_sel x_a0 x_a1 x_a2 x_a3 =
      (firstSome [EoCases.__smtx_ret_typeof_sel.case_0 x_a0 x_a1 x_a2 x_a3] default) := by
  conv => lhs; unfold __smtx_ret_typeof_sel
  unfold EoCases.__smtx_ret_typeof_sel.case_0
  logos_eq

theorem body_eo__24smtx_5fret_5ftypeof_5fsel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24smtx_5fret_5ftypeof_5fsel s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fret_5ftypeof_5fsel.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24smtx_5fret_5ftypeof_5fsel
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fret_5ftypeof_5fsel_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_ret_typeof_sel.case_0 splitting x_a0 x_a1 x_a2 x_a3

theorem eo__24smtx_5fret_5ftypeof_5fsel_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fret_5ftypeof_5fsel.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24smtx_5fret_5ftypeof_5fsel
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5fret_5ftypeof_5fsel s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__smtx_ret_typeof_sel x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fret_5ftypeof_5fsel_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_0
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s a1 h_a1 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s1 a2 h_a2 hinv1 h64 storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_0
  case_done hinv2 hG with h_v4 in EoCases.__smtx_ret_typeof_sel_rec.case_0 using

theorem case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_1
  pat_native_zero Store.native_pattern_nat_zero_spec s a1 h_a1 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_1
  pat_destruct_lit Store.native_pattern_succ_spec s1 a2 h_a2 hinv1 h64 as ⟨v8, x_v8, h_v8⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_1
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s2 e_v9 (by rw [he_v9]; rfl) h_v5 h_v2 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v8
  store_step with Store.native_nat_zero_spec s3 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v8 h_v9
  case_again hinv4 hG with h_v9 h_v10 h_v8 in EoCases.__smtx_ret_typeof_sel_rec.case_1 using

theorem case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_2
  pat_destruct_lit Store.native_pattern_succ_spec s a1 h_a1 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__smtx_ret_typeof_sel_rec.case_2
  case_again hinv1 hG with h_v2 h_v4 h_a2 in EoCases.__smtx_ret_typeof_sel_rec.case_2 using

theorem case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_ret_typeof_sel_rec.case_3 using

/-- logos's `__smtx_ret_typeof_sel_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fret_5ftypeof_5fsel_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2, EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2, EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_ret_typeof_sel_rec
  unfold EoCases.__smtx_ret_typeof_sel_rec.case_0 EoCases.__smtx_ret_typeof_sel_rec.case_1 EoCases.__smtx_ret_typeof_sel_rec.case_2 EoCases.__smtx_ret_typeof_sel_rec.case_3
  logos_eq

theorem step_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2 = __smtx_ret_typeof_sel_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fret_5ftypeof_5fsel_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  round_step with case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using
  round_step with case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0
  round_step with case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1
  round_step with case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s4 a0 a1 a2 x_a0 x_a1 x_a2 hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1 hc2
  round_stuck hinv5 hG using hc0 hc1 hc2 hc3 in EoCases.__smtx_ret_typeof_sel_rec.case_0 EoCases.__smtx_ret_typeof_sel_rec.case_1 EoCases.__smtx_ret_typeof_sel_rec.case_2 EoCases.__smtx_ret_typeof_sel_rec.case_3 splitting x_a0 x_a1 x_a2

theorem body_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24smtx_5fret_5ftypeof_5fsel_5frec body_eo__24smtx_5fret_5ftypeof_5fsel_5frec_loop
  step with step_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24smtx_5fret_5ftypeof_5fsel_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fret_5ftypeof_5fsel_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5fret_5ftypeof_5fsel_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 71#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24smtx_5fret_5ftypeof_5fsel_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_71 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_71 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf.case_0
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf.case_0 using

theorem case_1_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eFunType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf.case_1
  store_step with ih.eo__24smtx_5ftype_5fwf_5fcomponent s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftype_5fwf s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  case_done hinv3 hG with h_v5 in EoCases.__smtx_type_wf.case_1 using

theorem case_2_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5ftype_5fwf_5fcomponent s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_type_wf.case_2 using

/-- logos's `__smtx_type_wf` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftype_5fwf.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_type_wf x_a0 =
      (firstSome [EoCases.__smtx_type_wf.case_0 x_a0, EoCases.__smtx_type_wf.case_1 x_a0, EoCases.__smtx_type_wf.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_type_wf
  unfold EoCases.__smtx_type_wf.case_0 EoCases.__smtx_type_wf.case_1 EoCases.__smtx_type_wf.case_2
  logos_eq

theorem body_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftype_5fwf.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftype_5fwf_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24smtx_5ftype_5fwf_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  case_step with case_2_eo__24smtx_5ftype_5fwf_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_type_wf.case_0 EoCases.__smtx_type_wf.case_1 EoCases.__smtx_type_wf.case_2 splitting x_a0

theorem eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftype_5fwf.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftype_5fwf
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 72#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5ftype_5fwf s1 a0) (fun s' t => Represents.rep s' t (__smtx_type_wf x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_72 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_72 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftype_5fwf_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftype_5fwf_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftype_5fwf_5fcomponent s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_component.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_component.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftype_5fwf_5fcomponent
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5finhabited_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 a0 _ hinv1 h64 (hG.rem hrem) h_a0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.native_spec_and s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  rw [← Bridge.native_and] at h_v2
  case_done hinv3 hG with h_v2 in EoCases.__smtx_type_wf_component.case_0 using

/-- logos's `__smtx_type_wf_component` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftype_5fwf_5fcomponent.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_type_wf_component x_a0 =
      (firstSome [EoCases.__smtx_type_wf_component.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_type_wf_component
  unfold EoCases.__smtx_type_wf_component.case_0
  logos_eq

theorem body_eo__24smtx_5ftype_5fwf_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftype_5fwf_5fcomponent s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf_component x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftype_5fwf_5fcomponent.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftype_5fwf_5fcomponent
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftype_5fwf_5fcomponent_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_type_wf_component.case_0 splitting x_a0

theorem eo__24smtx_5ftype_5fwf_5fcomponent_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftype_5fwf_5fcomponent.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftype_5fwf_5fcomponent
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftype_5fwf_5fcomponent s1 a0) (fun s' t => Represents.rep s' t (__smtx_type_wf_component x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftype_5fwf_5fcomponent_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf_rec.case_0
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf_rec.case_0 using

theorem case_1_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf_rec.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf_rec.case_1 using

theorem case_2_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_2
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  store_step with ih.eo__24smtx_5finhabited_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  rw [← Bridge.native_and] at h_v8
  step as ⟨e_v9, he_v9⟩
  store_step with Store.native_spec_and s6 e_v9 (by rw [he_v9]; rfl) h_v5 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  rw [← Bridge.native_and] at h_v9
  case_done hinv7 hG with h_v9 in EoCases.__smtx_type_wf_rec.case_2 using

theorem case_3_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_3
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_and s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  rw [← Bridge.native_and] at h_v4
  case_done hinv3 hG with h_v4 in EoCases.__smtx_type_wf_rec.case_3 using

theorem case_4_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_4
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_and s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  rw [← Bridge.native_and] at h_v4
  case_done hinv3 hG with h_v4 in EoCases.__smtx_type_wf_rec.case_4 using

theorem case_5_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_5
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdecl_5fwf_5frec s1 v2 v2 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  case_done hinv3 hG with h_v5 in EoCases.__smtx_type_wf_rec.case_5 using

theorem case_6_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_6
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_type_wf_rec.case_6 using

theorem case_7_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eFunType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_7
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_type_wf_rec.case_7 using

theorem case_8_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_8
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_type_wf_rec.case_8 using

theorem case_9_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_type_wf_rec.case_9 using

theorem cases_0_0_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_0 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_1 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_2 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_0 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_1 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_2 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24smtx_5ftype_5fwf_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_4 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_5 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_6 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_5 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_6 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24smtx_5ftype_5fwf_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_8 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_8 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_none hinv2 hG with ⟨hl_8, hl_9⟩

/-- logos's `__smtx_type_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftype_5fwf_5frec.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_type_wf_rec x_a0 =
      (firstSome [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_type_wf_rec
  unfold EoCases.__smtx_type_wf_rec.case_0 EoCases.__smtx_type_wf_rec.case_1 EoCases.__smtx_type_wf_rec.case_2 EoCases.__smtx_type_wf_rec.case_3 EoCases.__smtx_type_wf_rec.case_4 EoCases.__smtx_type_wf_rec.case_5 EoCases.__smtx_type_wf_rec.case_6 EoCases.__smtx_type_wf_rec.case_7 EoCases.__smtx_type_wf_rec.case_8 EoCases.__smtx_type_wf_rec.case_9
  logos_eq

theorem body_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf_rec x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftype_5fwf_5frec.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  body_group_step with cases_0_0_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_step with cases_0_1_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_8, hl_9⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 in EoCases.__smtx_type_wf_rec.case_0 EoCases.__smtx_type_wf_rec.case_1 EoCases.__smtx_type_wf_rec.case_2 EoCases.__smtx_type_wf_rec.case_3 EoCases.__smtx_type_wf_rec.case_4 EoCases.__smtx_type_wf_rec.case_5 EoCases.__smtx_type_wf_rec.case_6 EoCases.__smtx_type_wf_rec.case_7 EoCases.__smtx_type_wf_rec.case_8 EoCases.__smtx_type_wf_rec.case_9 splitting x_a0

theorem eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftype_5fwf_5frec.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftype_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 74#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5ftype_5fwf_5frec s1 a0) (fun s' t => Represents.rep s' t (__smtx_type_wf_rec x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_74 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_74 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftype_5fwf_5frec_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eBoolean.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof.case_0 using

theorem case_1_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof.case_1 using

theorem case_2_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eRational.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof.case_2 using

theorem case_3_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eString.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with Store.native_spec_string_valid s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  rw [← Bridge.native_string_valid] at h_v2
  have h_ite_v6 := (show if_0_eo__24smtx_5ftypeof s1 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v2 with ⟨hx_3, hbv_3⟩ | ⟨hx_3, hbv_3⟩
    · ite_branch hbv_3
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
      ite_done hinv3 hG with (native_ite_true_rep _ hx_3 h_v4)
    · ite_branch hbv_3
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_3 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v6 in EoCases.__smtx_typeof.case_3 using

theorem case_4_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eBinary.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_4
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_zleq s1 e_v4 (by rw [he_v4]; rfl) h_v3 h_v1 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  rw [← Bridge.native_zleq] at h_v4
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_int_pow2 s2 e_v5 (by rw [he_v5]; rfl) h_v1 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_int_pow2] at h_v5
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_mod_total s3 e_v6 (by rw [he_v6]; rfl) h_v2 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  rw [← Bridge.native_mod_total] at h_v6
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_zeq s4 e_v7 (by rw [he_v7]; rfl) h_v2 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  rw [← Bridge.native_zeq] at h_v7
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s5 e_v8 (by rw [he_v8]; rfl) h_v4 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  rw [← Bridge.native_and] at h_v8
  have h_ite_v12 := (show if_1_eo__24smtx_5ftypeof s6 v8 v1 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
    · ite_branch hbv_9
      step as ⟨e_v9, he_v9⟩
      store_step with Store.native_spec_int_to_nat s6 e_v9 (by rw [he_v9]; rfl) h_v1 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      rw [← Bridge.native_int_to_nat] at h_v9
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s7 e_v10 (by rw [he_v10]; rfl) h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      ite_done hinv8 hG with (native_ite_true_rep _ hx_9 h_v10)
    · ite_branch hbv_9
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v11 (by rw [he_v11]; exact empty_args) hinv6 h64 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v11))
  store_step with h_ite_v12 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv7 hG with h_v12 in EoCases.__smtx_typeof.case_4 using

theorem case_5_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2enot.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_5
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_2_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_5 using

theorem case_6_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eand.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_6
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_4_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_4_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_3_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_3_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_6 using

theorem case_7_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eor.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_7
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_6_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_6_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_5_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_5_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_7 using

theorem case_8_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3d_3e.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_8
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_8_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_8_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_7_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_7_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_8 using

theorem case_9_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3d.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_9
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5f_3d s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_9 using

theorem case_10_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_10_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eite.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_10
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fite s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_10 using

theorem case_11_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_11_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_11
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5fdd_5flookup s2 v1 v2 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v2 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5fdt_5fresolve s3 v6 v2 _ _ hinv3 h64 (hG.rem hrem) h_v6 h_v2 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s4 v5 v7 v3 _ _ _ hinv4 h64 (hG.rem hrem) h_v5 h_v7 h_v3 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s5 v4 v8 _ _ hinv5 h64 (hG.rem hrem) h_v4 h_v8 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv6 hG with h_v9 in EoCases.__smtx_typeof.case_11 using

theorem case_12_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_12_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eApply.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_12
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtSel.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ ⟨v6, x_v6, h_v6⟩ ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__smtx_typeof.case_12
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel s v4 v5 v6 v7 _ _ _ _ hinv h64 hrem h_v4 h_v5 h_v6 h_v7 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v9 (by rw [he_v9]; rfl) h_v4 h_v5 hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel s2 v4 v5 v6 v7 _ _ _ _ hinv2 h64 (hG.rem hrem) h_v4 h_v5 h_v6 h_v7 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s3 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24smtx_5ftypeof_5fapply s5 v11 v12 _ _ hinv5 h64 (hG.rem hrem) h_v11 h_v12 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s6 v8 v13 _ _ hinv6 h64 (hG.rem hrem) h_v8 h_v13 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv7 hG with h_v14 in EoCases.__smtx_typeof.case_12 using

theorem case_13_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_13_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eApply.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_13
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtTester.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ ⟨v6, x_v6, h_v6⟩ else hinv hG in EoCases.__smtx_typeof.case_13
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v7 (by rw [he_v7]; rfl) h_v4 h_v5 hinv h64 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5fdd_5flookup s1 v4 v5 _ _ hinv1 h64 (hG.rem hrem) h_v4 h_v5 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24smtx_5fdt_5fresolve s2 v8 v5 _ _ hinv2 h64 (hG.rem hrem) h_v8 h_v5 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s3 v7 v9 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v9 h_v6 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s4 e_v11 (by rw [he_v11]; rfl) h_v4 h_v5 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s5 e_v12 (by rw [he_v12]; exact empty_args) hinv5 h64 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s6 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv6 h64 as ⟨v13, s7, hinv7, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24smtx_5ftypeof s7 v2 _ hinv7 h64 (hG.rem hrem) h_v2 as ⟨v14, s8, hinv8, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with ih.eo__24smtx_5ftypeof_5fapply s8 v13 v14 _ _ hinv8 h64 (hG.rem hrem) h_v13 h_v14 as ⟨v15, s9, hinv9, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with ih.eo__24smtx_5ftypeof_5fguard s9 v10 v15 _ _ hinv9 h64 (hG.rem hrem) h_v10 h_v15 as ⟨v16, s10, hinv10, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  case_done hinv10 hG with h_v16 in EoCases.__smtx_typeof.case_13 using

theorem case_14_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_14_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eApply.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_14
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fapply s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_14 using

theorem case_15_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_15_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_15 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_15
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s v2 v2 _ _ hinv h64 hrem h_v2 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_typeof.case_15 using

theorem case_16_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_16_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_16 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eUConst.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_16
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s v2 v2 _ _ hinv h64 hrem h_v2 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_typeof.case_16 using

theorem case_17_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_17_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof.case_17 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_17 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_17_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof.case_17 using

theorem cases_0_0_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_0 x_a0 = none ∧ EoCases.__smtx_typeof.case_1 x_a0 = none ∧ EoCases.__smtx_typeof.case_2 x_a0 = none ∧ EoCases.__smtx_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [] ++ [EoCases.__smtx_typeof.case_0 x_a0] ++ [EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0] ++ [EoCases.__smtx_typeof.case_1 x_a0] ++ [EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0] ++ [EoCases.__smtx_typeof.case_2 x_a0] ++ [EoCases.__smtx_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0] ++ [EoCases.__smtx_typeof.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_4 x_a0 = none ∧ EoCases.__smtx_typeof.case_5 x_a0 = none ∧ EoCases.__smtx_typeof.case_6 x_a0 = none ∧ EoCases.__smtx_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [] ++ [EoCases.__smtx_typeof.case_4 x_a0] ++ [EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [EoCases.__smtx_typeof.case_4 x_a0] ++ [EoCases.__smtx_typeof.case_5 x_a0] ++ [EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0] ++ [EoCases.__smtx_typeof.case_6 x_a0] ++ [EoCases.__smtx_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0] ++ [EoCases.__smtx_typeof.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_8 x_a0 = none ∧ EoCases.__smtx_typeof.case_9 x_a0 = none ∧ EoCases.__smtx_typeof.case_10 x_a0 = none ∧ EoCases.__smtx_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [] ++ [EoCases.__smtx_typeof.case_8 x_a0] ++ [EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [EoCases.__smtx_typeof.case_8 x_a0] ++ [EoCases.__smtx_typeof.case_9 x_a0] ++ [EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_step with case_10_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0] ++ [EoCases.__smtx_typeof.case_10 x_a0] ++ [EoCases.__smtx_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hl_8 hl_9
  group_step with case_11_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0] ++ [EoCases.__smtx_typeof.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_3_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_12 x_a0 = none ∧ EoCases.__smtx_typeof.case_13 x_a0 = none ∧ EoCases.__smtx_typeof.case_14 x_a0 = none ∧ EoCases.__smtx_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [] ++ [EoCases.__smtx_typeof.case_12 x_a0] ++ [EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using
  group_step with case_13_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_12 x_a0] ++ [EoCases.__smtx_typeof.case_13 x_a0] ++ [EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hl_12
  group_step with case_14_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0] ++ [EoCases.__smtx_typeof.case_14 x_a0] ++ [EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_14⟩ using hl_12 hl_13
  group_step with case_15_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0] ++ [EoCases.__smtx_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_4_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_16 x_a0 = none ∧ EoCases.__smtx_typeof.case_17 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_16_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] = [] ++ [EoCases.__smtx_typeof.case_16 x_a0] ++ [EoCases.__smtx_typeof.case_17 x_a0] from rfl)
    otherwise ⟨hl_16⟩ using
  group_step with case_17_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] = [EoCases.__smtx_typeof.case_16 x_a0] ++ [EoCases.__smtx_typeof.case_17 x_a0] ++ [] from rfl)
    otherwise ⟨hl_17⟩ using hl_16
  group_none hinv2 hG with ⟨hl_16, hl_17⟩

theorem cases_1_0_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_0_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_0 x_a0 = none ∧ EoCases.__smtx_typeof.case_1 x_a0 = none ∧ EoCases.__smtx_typeof.case_2 x_a0 = none ∧ EoCases.__smtx_typeof.case_3 x_a0 = none ∧ EoCases.__smtx_typeof.case_4 x_a0 = none ∧ EoCases.__smtx_typeof.case_5 x_a0 = none ∧ EoCases.__smtx_typeof.case_6 x_a0 = none ∧ EoCases.__smtx_typeof.case_7 x_a0 = none ∧ EoCases.__smtx_typeof.case_8 x_a0 = none ∧ EoCases.__smtx_typeof.case_9 x_a0 = none ∧ EoCases.__smtx_typeof.case_10 x_a0 = none ∧ EoCases.__smtx_typeof.case_11 x_a0 = none ∧ EoCases.__smtx_typeof.case_12 x_a0 = none ∧ EoCases.__smtx_typeof.case_13 x_a0 = none ∧ EoCases.__smtx_typeof.case_14 x_a0 = none ∧ EoCases.__smtx_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_0_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [] ++ [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] ++ [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  group_step with cases_0_1_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] ++ [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] ++ [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  group_step with cases_0_2_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] ++ [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] ++ [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_step with cases_0_3_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] ++ [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_1_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_16 x_a0 = none ∧ EoCases.__smtx_typeof.case_17 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_4_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] = [] ++ [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] ++ [] from rfl)
    otherwise ⟨hl_16, hl_17⟩ using
  group_none hinv1 hG with ⟨hl_16, hl_17⟩

/-- logos's `__smtx_typeof` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_typeof x_a0 =
      (firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] default) := by
  conv => lhs; unfold __smtx_typeof
  unfold EoCases.__smtx_typeof.case_0 EoCases.__smtx_typeof.case_1 EoCases.__smtx_typeof.case_2 EoCases.__smtx_typeof.case_3 EoCases.__smtx_typeof.case_4 EoCases.__smtx_typeof.case_5 EoCases.__smtx_typeof.case_6 EoCases.__smtx_typeof.case_7 EoCases.__smtx_typeof.case_8 EoCases.__smtx_typeof.case_9 EoCases.__smtx_typeof.case_10 EoCases.__smtx_typeof.case_11 EoCases.__smtx_typeof.case_12 EoCases.__smtx_typeof.case_13 EoCases.__smtx_typeof.case_14 EoCases.__smtx_typeof.case_15 EoCases.__smtx_typeof.case_16 EoCases.__smtx_typeof.case_17
  logos_eq

theorem body_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  body_group_step with cases_1_0_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] = [] ++ [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] ++ [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using
  body_group_step with cases_1_1_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] ++ [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] ++ [] from rfl)
    otherwise ⟨hl_16, hl_17⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  body_stuck hinv2 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 in EoCases.__smtx_typeof.case_0 EoCases.__smtx_typeof.case_1 EoCases.__smtx_typeof.case_2 EoCases.__smtx_typeof.case_3 EoCases.__smtx_typeof.case_4 EoCases.__smtx_typeof.case_5 EoCases.__smtx_typeof.case_6 EoCases.__smtx_typeof.case_7 EoCases.__smtx_typeof.case_8 EoCases.__smtx_typeof.case_9 EoCases.__smtx_typeof.case_10 EoCases.__smtx_typeof.case_11 EoCases.__smtx_typeof.case_12 EoCases.__smtx_typeof.case_13 EoCases.__smtx_typeof.case_14 EoCases.__smtx_typeof.case_15 EoCases.__smtx_typeof.case_16 EoCases.__smtx_typeof.case_17 splitting x_a0

theorem eo__24smtx_5ftypeof_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftypeof
  apply WP.dspec_mono (Store.framed_type_cached s hinv hrem h64 cache.TypeCacheKind.Smt a0
    (fun s1 => body_eo__24smtx_5ftypeof s1 a0) (fun s' t => Represents.rep s' t (__smtx_typeof x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_4294967297 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_4294967297 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.native_spec_Teq s e_v0 (by rw [he_v0]; rfl) h_a0 h_a1 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  have h_ite_v3 := (show if_0_eo__24smtx_5ftypeof_5f_3d s1 v0 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5f_3d
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v0 with ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩
    · ite_branch hbv_1
      step as ⟨e_v1, he_v1⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
      ite_done hinv2 hG with (native_ite_true_rep _ hx_1 h_v1)
    · ite_branch hbv_1
      step as ⟨e_v2, he_v2⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v2 (by rw [he_v2]; exact empty_args) hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0
      ite_done hinv2 hG with (native_ite_false_rep _ hx_1 h_v2))
  store_step with h_ite_v3 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with ih.eo__24smtx_5ftypeof_5fguard s2 a0 v3 _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof_eq.case_0 using

/-- logos's `__smtx_typeof_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5f_3d.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_eq x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_eq.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_eq
  unfold EoCases.__smtx_typeof_eq.case_0
  logos_eq

theorem body_eo__24smtx_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5f_3d.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5f_3d_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_typeof_eq.case_0 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5f_3d_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5f_3d.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5f_3d
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5f_3d s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5f_3d_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_apply.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_apply.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eFunType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_apply.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_Teq s e_v3 (by rw [he_v3]; rfl) h_v1 h_a1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  have h_ite_v5 := (show if_0_eo__24smtx_5ftypeof_5fapply s1 v3 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fapply
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      ite_done hinv1 hG with (native_ite_true_rep _ hx_4 h_v2)
    · ite_branch hbv_4
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (native_ite_false_rep _ hx_4 h_v4))
  store_step with h_ite_v5 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fguard s2 v1 v5 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v5 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__smtx_typeof_apply.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_apply.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_apply.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_apply.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_Teq s e_v3 (by rw [he_v3]; rfl) h_v1 h_a1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  have h_ite_v5 := (show if_1_eo__24smtx_5ftypeof_5fapply s1 v3 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fapply
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      ite_done hinv1 hG with (native_ite_true_rep _ hx_4 h_v2)
    · ite_branch hbv_4
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (native_ite_false_rep _ hx_4 h_v4))
  store_step with h_ite_v5 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fguard s2 v1 v5 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v5 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__smtx_typeof_apply.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_apply.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_apply.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_apply.case_2 using

/-- logos's `__smtx_typeof_apply` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fapply.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_apply x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_apply.case_0 x_a0 x_a1, EoCases.__smtx_typeof_apply.case_1 x_a0 x_a1, EoCases.__smtx_typeof_apply.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_apply
  unfold EoCases.__smtx_typeof_apply.case_0 EoCases.__smtx_typeof_apply.case_1 EoCases.__smtx_typeof_apply.case_2
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_apply x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fapply.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fapply_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fapply_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5ftypeof_5fapply_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_typeof_apply.case_0 EoCases.__smtx_typeof_apply.case_1 EoCases.__smtx_typeof_apply.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fapply.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fapply
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fapply s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_apply x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fapply_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_dt_cons_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s1 a2 h_a2 hinv1 h64 storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 in EoCases.__smtx_typeof_dt_cons_rec.case_0
  case_done hinv2 hG with h_a0 in EoCases.__smtx_typeof_dt_cons_rec.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_1
  pat_native_zero Store.native_pattern_nat_zero_spec s a2 h_a2 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_typeof_dt_cons_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s1 e_v7 (by rw [he_v7]; rfl) h_v5 h_v2 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  store_step with Store.native_nat_zero_spec s2 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s3 a0 v7 v8 _ _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDtcAppType.construct s4 e_v10 (by rw [he_v10]; rfl) h_v4 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__smtx_typeof_dt_cons_rec.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_2
  pat_destruct_lit Store.native_pattern_succ_spec s a2 h_a2 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__smtx_typeof_dt_cons_rec.case_2
  case_again hinv1 hG with h_a0 h_v2 h_v4 in EoCases.__smtx_typeof_dt_cons_rec.case_2 using

theorem case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_dt_cons_rec.case_3 using

/-- logos's `__smtx_typeof_dt_cons_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fdt_5fcons_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_dt_cons_rec
  unfold EoCases.__smtx_typeof_dt_cons_rec.case_0 EoCases.__smtx_typeof_dt_cons_rec.case_1 EoCases.__smtx_typeof_dt_cons_rec.case_2 EoCases.__smtx_typeof_dt_cons_rec.case_3
  logos_eq

theorem step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2 = __smtx_typeof_dt_cons_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fdt_5fcons_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  round_step with case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using
  round_step with case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0
  round_step with case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1
  round_step with case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s4 a0 a1 a2 x_a0 x_a1 x_a2 hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1 hc2
  round_stuck hinv5 hG using hc0 hc1 hc2 hc3 in EoCases.__smtx_typeof_dt_cons_rec.case_0 EoCases.__smtx_typeof_dt_cons_rec.case_1 EoCases.__smtx_typeof_dt_cons_rec.case_2 EoCases.__smtx_typeof_dt_cons_rec.case_3 splitting x_a0 x_a1 x_a2

theorem body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_loop
  step with step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fdt_5fcons_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 78#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_78 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_78 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fguard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fguard s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_guard.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_guard.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fguard
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with Store.native_spec_Teq s1 e_v1 (by rw [he_v1]; rfl) h_a0 h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  have h_ite_v3 := (show if_0_eo__24smtx_5ftypeof_5fguard s2 v1 a1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fguard
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      step as ⟨e_v2, he_v2⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
      ite_done hinv3 hG with (native_ite_true_rep _ hx_2 h_v2)
    · ite_branch hbv_2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_2 h_a1))
  store_step with h_ite_v3 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v3 in EoCases.__smtx_typeof_guard.case_0 using

/-- logos's `__smtx_typeof_guard` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fguard.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_guard x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_guard.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_guard
  unfold EoCases.__smtx_typeof_guard.case_0
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fguard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fguard s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_guard x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fguard.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fguard
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fguard_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_typeof_guard.case_0 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fguard_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fguard.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fguard
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fguard s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_guard x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fguard_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fguard_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fguard_5fwf s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_guard_wf.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_guard_wf.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fguard_5fwf
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5ftype_5fwf s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  have h_ite_v2 := (show if_0_eo__24smtx_5ftypeof_5fguard_5fwf s1 v0 a1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fguard_5fwf
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v0 with ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩
    · ite_branch hbv_1
      ite_done hinv1 hG with (native_ite_true_rep _ hx_1 h_a1)
    · ite_branch hbv_1
      step as ⟨e_v1, he_v1⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
      ite_done hinv2 hG with (native_ite_false_rep _ hx_1 h_v1))
  store_step with h_ite_v2 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v2 in EoCases.__smtx_typeof_guard_wf.case_0 using

/-- logos's `__smtx_typeof_guard_wf` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fguard_5fwf.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_guard_wf x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_guard_wf.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_guard_wf
  unfold EoCases.__smtx_typeof_guard_wf.case_0
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fguard_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fguard_5fwf s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_guard_wf x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fguard_5fwf.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fguard_5fwf
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fguard_5fwf_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_typeof_guard_wf.case_0 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fguard_5fwf_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fguard_5fwf.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fguard_5fwf
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fguard_5fwf s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_guard_wf x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fguard_5fwf_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_ite.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_ite.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fite
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_ite.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.native_spec_Teq s1 e_v1 (by rw [he_v1]; rfl) h_a1 h_a2 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  have h_ite_v3 := (show if_0_eo__24smtx_5ftypeof_5fite s2 v1 a1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fite
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      ite_done hinv2 hG with (native_ite_true_rep _ hx_2 h_a1)
    · ite_branch hbv_2
      step as ⟨e_v2, he_v2⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
      ite_done hinv3 hG with (native_ite_false_rep _ hx_2 h_v2))
  store_step with h_ite_v3 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v3 in EoCases.__smtx_typeof_ite.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_ite.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_ite.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fite
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_ite.case_1 using

/-- logos's `__smtx_typeof_ite` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fite.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_ite x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_ite.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_ite.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_ite
  unfold EoCases.__smtx_typeof_ite.case_0 EoCases.__smtx_typeof_ite.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fite.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fite
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fite_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fite_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_ite.case_0 EoCases.__smtx_typeof_ite.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fite.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fite
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fite s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_ite x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fite_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- **Every program with a generated proof computes what logos's function does.** -/
theorem specs (n : Nat) : Specs n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    exact ⟨eo__24eo_5fStateObj_5fproven_spec n ih,
      eo__24eo_5fchecker_5fis_5frefutation_spec n ih,
      eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec n ih,
      eo__24eo_5fcmd_5fstep_5fproven_spec n ih,
      eo__24eo_5fdd_5flookup_spec n ih,
      eo__24eo_5fdd_5fresolve_spec n ih,
      eo__24eo_5fdt_5fresolve_spec n ih,
      eo__24eo_5fdtc_5fresolve_spec n ih,
      eo__24eo_5finvoke_5fassume_5flist_spec n ih,
      eo__24eo_5finvoke_5fcmd_spec n ih,
      eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec n ih,
      eo__24eo_5finvoke_5fcmd_5flist_spec n ih,
      eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih,
      eo__24eo_5fis_5fbool_5ftype_spec n ih,
      eo__24eo_5fis_5fclosed_spec n ih,
      eo__24eo_5fis_5fclosed_5frec_spec n ih,
      eo__24eo_5fis_5flist_5fnil_spec n ih,
      eo__24eo_5flit_5ftype_5fBinary_spec n ih,
      eo__24eo_5flit_5ftype_5fNumeral_spec n ih,
      eo__24eo_5flit_5ftype_5fRational_spec n ih,
      eo__24eo_5flit_5ftype_5fString_spec n ih,
      eo__24eo_5fmk_5fpremise_5flist_spec n ih,
      eo__24eo_5fnil_spec n ih,
      eo__24eo_5fprog_5fcontra_spec n ih,
      eo__24eo_5fprog_5frefl_spec n ih,
      eo__24eo_5fprog_5fscope_spec n ih,
      eo__24eo_5fprog_5fsymm_spec n ih,
      eo__24eo_5fprog_5ftrans_spec n ih,
      eo__24eo_5fpush_5fassume_5fcheck_spec n ih,
      eo__24eo_5fpush_5finput_5fassume_5fcheck_spec n ih,
      eo__24eo_5fpush_5fproven_spec n ih,
      eo__24eo_5fpush_5fproven_5fcheck_spec n ih,
      eo__24eo_5fstate_5fis_5fclosed_spec n ih,
      eo__24eo_5fstate_5fis_5frefutation_spec n ih,
      eo__24eo_5fstate_5fproven_5fnth_spec n ih,
      eo__24eo_5fto_5fsmt_spec n ih,
      eo__24eo_5fto_5fsmt_5fdatatype_spec n ih,
      eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec n ih,
      eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec n ih,
      eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec n ih,
      eo__24eo_5fto_5fsmt_5ftype_spec n ih,
      eo__24eo_5ftypeof_spec n ih,
      eo__24eo_5ftypeof_5f_3d_spec n ih,
      eo__24eo_5ftypeof_5fBitVec_spec n ih,
      eo__24eo_5ftypeof_5fSeq_spec n ih,
      eo__24eo_5ftypeof_5fand_spec n ih,
      eo__24eo_5ftypeof_5fapply_spec n ih,
      eo__24eo_5ftypeof_5fdt_5fcons_5frec_spec n ih,
      eo__24eo_5ftypeof_5fdt_5fsel_5freturn_spec n ih,
      eo__24eo_5ftypeof_5ffun_5ftype_spec n ih,
      eo__24eo_5ftypeof_5fnot_spec n ih,
      eo__24mk_5fsymm_spec n ih,
      eo__24mk_5ftrans_spec n ih,
      eo__24smtx_5fdd_5fhas_5fdt_spec n ih,
      eo__24smtx_5fdd_5flookup_spec n ih,
      eo__24smtx_5fdecl_5finhabited_spec n ih,
      eo__24smtx_5fdecl_5fwf_5frec_spec n ih,
      eo__24smtx_5fdt_5fcons_5finhabited_spec n ih,
      eo__24smtx_5fdt_5fcons_5fwf_5frec_spec n ih,
      eo__24smtx_5fdt_5finhabited_spec n ih,
      eo__24smtx_5fdt_5fresolve_spec n ih,
      eo__24smtx_5fdt_5fwf_5frec_spec n ih,
      eo__24smtx_5fdtc_5fresolve_spec n ih,
      eo__24smtx_5finhabited_5ftype_spec n ih,
      eo__24smtx_5fret_5ftypeof_5fsel_spec n ih,
      eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih,
      eo__24smtx_5ftype_5fwf_spec n ih,
      eo__24smtx_5ftype_5fwf_5fcomponent_spec n ih,
      eo__24smtx_5ftype_5fwf_5frec_spec n ih,
      eo__24smtx_5ftypeof_spec n ih,
      eo__24smtx_5ftypeof_5f_3d_spec n ih,
      eo__24smtx_5ftypeof_5fapply_spec n ih,
      eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih,
      eo__24smtx_5ftypeof_5fguard_spec n ih,
      eo__24smtx_5ftypeof_5fguard_5fwf_spec n ih,
      eo__24smtx_5ftypeof_5fite_spec n ih⟩

end pathos_compiled_checker
