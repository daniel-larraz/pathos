module
public import CpcProofs.Head
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

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option maxRecDepth 8000

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result
open Eo hiding Term
open Smtm
open generated generated.part0 generated.part1 generated.part2 generated.part3 generated.part4 generated.part5 generated.part6 generated.part7 generated.part8 generated.part9 generated.part10 generated.part11 generated.part12

set_option maxRecDepth 20000 in
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise.rust_eq_20000 (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __bv_mk_bitblast_step_bitwise x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_bitwise.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__bv_mk_bitblast_step_bitwise.case_1 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_bitwise
  unfold EoCases.__bv_mk_bitblast_step_bitwise.case_0 EoCases.__bv_mk_bitblast_step_bitwise.case_1
  try unfold Eo.__eo_l_1___bv_mk_bitblast_step_bitwise
  logos_eq_deep

set_option maxRecDepth 20000 in
theorem eo__24is_5feq_5fmaybe_5fto_5freal.rust_eq_20000 (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __is_eq_maybe_to_real x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_eq_maybe_to_real.case_0 x_a0 x_a1, EoCases.__is_eq_maybe_to_real.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __is_eq_maybe_to_real
  unfold EoCases.__is_eq_maybe_to_real.case_0 EoCases.__is_eq_maybe_to_real.case_1
  try unfold Eo.__eo_l_1___is_eq_maybe_to_real
  logos_eq_deep

set_option maxRecDepth 64000 in
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise.rust_eq_64000 (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __bv_mk_bitblast_step_bitwise x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_bitwise.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__bv_mk_bitblast_step_bitwise.case_1 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_bitwise
  unfold EoCases.__bv_mk_bitblast_step_bitwise.case_0 EoCases.__bv_mk_bitblast_step_bitwise.case_1
  try unfold Eo.__eo_l_1___bv_mk_bitblast_step_bitwise
  logos_eq_deep

set_option maxRecDepth 64000 in
theorem eo__24is_5feq_5fmaybe_5fto_5freal.rust_eq_64000 (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __is_eq_maybe_to_real x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_eq_maybe_to_real.case_0 x_a0 x_a1, EoCases.__is_eq_maybe_to_real.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __is_eq_maybe_to_real
  unfold EoCases.__is_eq_maybe_to_real.case_0 EoCases.__is_eq_maybe_to_real.case_1
  try unfold Eo.__eo_l_1___is_eq_maybe_to_real
  logos_eq_deep

end pathos_compiled_checker
