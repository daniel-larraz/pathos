module

public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtTranslate
import all CpcMini.SmtTranslate
public import CpcMini.SmtModel
import all CpcMini.SmtModel

/-!
The cases of the programs, one function each, as a backend that tries a
program's cases in order computes them: `some` of the case's result where
its pattern matches, `none` where it does not. A parameter that the
program's pattern repeats is a test for equality here, and a failed test is
"no match". The programs themselves (Logos.lean and the modules beside it)
say the same with linear patterns, requirements and continuation programs.

Nothing in the checker uses these definitions. They are for relating
another backend's code, case by case, to the programs.
-/

@[expose] public section

open SmtEval
open Eo
open Smtm

set_option linter.unusedVariables false
set_option linter.internalConstructors false
set_option maxHeartbeats 10000000

noncomputable section

namespace EoCases

def __eo_mk_apply.case_0 : Term -> Term -> Option (Term)
  | x1, x2 => some ((Term.Apply x1 x2))

def __eo_and.case_0 : Term -> Term -> Option (Term)
  | (Term.Boolean b1), (Term.Boolean b2) => some ((Term.Boolean (native_and b1 b2)))
  | _, _ => none

def __eo_and.case_1 : Term -> Term -> Option (Term)
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => some ((__eo_requires (Term.Numeral w1) (Term.Numeral w2) (Term.Binary w1 (native_mod_total (native_binary_and w1 n1 n2) (native_int_pow2 w1)))))
  | _, _ => none

def __eo_len.case_0 : Term -> Option (Term)
  | (Term.String s1) => some ((Term.Numeral (native_str_len s1)))
  | _ => none

def __eo_len.case_1 : Term -> Option (Term)
  | (Term.Binary w n1) => some ((Term.Numeral w))
  | _ => none

def __eo_eq.case_0 : Term -> Term -> Option (Term)
  | t, s => some ((Term.Boolean (native_teq s t)))

def __eo_dtc_resolve.case_0 : DatatypeCons -> DatatypeDecl -> Option (DatatypeCons)
  | (DatatypeCons.cons (Term.DatatypeTypeRef s) c), dd => some ((DatatypeCons.cons (Term.DatatypeType s dd) (__eo_dtc_resolve c dd)))
  | _, _ => none

def __eo_dtc_resolve.case_1 : DatatypeCons -> DatatypeDecl -> Option (DatatypeCons)
  | (DatatypeCons.cons T c), dd => some ((DatatypeCons.cons T (__eo_dtc_resolve c dd)))
  | _, _ => none

def __eo_dtc_resolve.case_2 : DatatypeCons -> DatatypeDecl -> Option (DatatypeCons)
  | DatatypeCons.unit, dd => some (DatatypeCons.unit)
  | _, _ => none

def __eo_dt_resolve.case_0 : Datatype -> DatatypeDecl -> Option (Datatype)
  | (Datatype.sum c d), dd => some ((Datatype.sum (__eo_dtc_resolve c dd) (__eo_dt_resolve d dd)))
  | _, _ => none

def __eo_dt_resolve.case_1 : Datatype -> DatatypeDecl -> Option (Datatype)
  | Datatype.null, dd => some (Datatype.null)
  | _, _ => none

def __eo_dd_lookup.case_0 : native_String -> DatatypeDecl -> Option (Datatype)
  | s, (DatatypeDecl.cons s2 d dd) => some ((native_ite (native_streq s s2) d (__eo_dd_lookup s dd)))
  | _, _ => none

def __eo_dd_lookup.case_1 : native_String -> DatatypeDecl -> Option (Datatype)
  | s, DatatypeDecl.nil => some (Datatype.null)
  | _, _ => none

def __eo_dd_resolve.case_0 : native_String -> DatatypeDecl -> Option (Datatype)
  | s, dd => some ((__eo_dt_resolve (__eo_dd_lookup s dd) dd))

def __eo_is_bool_type.case_0 : Term -> Option (Term)
  | x => some ((__eo_eq (__eo_typeof x) Term.Bool))

def __eo_get_nil_rec.case_0 : Term -> Term -> Option (Term)
  | f, (Term.Apply (Term.Apply g x) y) => some ((__eo_requires f g (__eo_get_nil_rec f y)))
  | _, _ => none

def __eo_get_nil_rec.case_1 : Term -> Term -> Option (Term)
  | f, nil => some ((__eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil))

def __eo_is_list.case_0 : Term -> Term -> Option (Term)
  | f, x => some ((__eo_is_ok (__eo_get_nil_rec f x)))

def __eo_prog_scope.case_0 : Term -> Proof -> Option (Term)
  | F, (Proof.pf G) => some ((Term.Apply (Term.Apply (Term.UOp UserOp.imp) F) G))
  | _, _ => none

def __eo_prog_contra.case_0 : Proof -> Proof -> Option (Term)
  | (Proof.pf F), (Proof.pf (Term.Apply (Term.UOp UserOp.not) __eo_lv_F_2)) => if F = __eo_lv_F_2 then some ((Term.Boolean false)) else none
  | _, _ => none

def __eo_prog_refl.case_0 : Term -> Option (Term)
  | t => some ((Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) t))

def __mk_symm.case_0 : Term -> Option (Term)
  | (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2) => some ((Term.Apply (Term.Apply (Term.UOp UserOp.eq) t2) t1))
  | _ => none

def __mk_symm.case_1 : Term -> Option (Term)
  | (Term.Apply (Term.UOp UserOp.not) (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2)) => some ((Term.Apply (Term.UOp UserOp.not) (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t2) t1)))
  | _ => none

def __eo_prog_symm.case_0 : Proof -> Option (Term)
  | (Proof.pf F) => some ((__mk_symm F))
  | _ => none

def __mk_trans.case_0 : Term -> Term -> Term -> Option (Term)
  | t1, t2, (Term.Apply (Term.Apply (Term.UOp UserOp.and) (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t3) t4)) tail) => some ((__eo_requires t2 t3 (__mk_trans t1 t4 tail)))
  | _, _, _ => none

def __mk_trans.case_1 : Term -> Term -> Term -> Option (Term)
  | t1, t2, (Term.Boolean true) => some ((Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
  | _, _, _ => none

def __eo_prog_trans.case_0 : Proof -> Option (Term)
  | (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.and) (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2)) tail)) => some ((__mk_trans t1 t2 tail))
  | _ => none

def __eo_nil.case_0 : Term -> Term -> Option (Term)
  | (Term.UOp UserOp.and), T => some ((Term.Boolean true))
  | _, _ => none

def __eo_nil.case_1 : Term -> Term -> Option (Term)
  | Term.__eo_List_cons, Term.__eo_List => some (Term.__eo_List_nil)
  | _, _ => none

def __eo_is_list_nil.case_0 : Term -> Term -> Option (Term)
  | (Term.UOp UserOp.and), (Term.Boolean true) => some ((Term.Boolean true))
  | _, _ => none

def __eo_is_list_nil.case_1 : Term -> Term -> Option (Term)
  | Term.__eo_List_cons, Term.__eo_List_nil => some ((Term.Boolean true))
  | _, _ => none

def __eo_is_list_nil.case_2 : Term -> Term -> Option (Term)
  | f, nil => some ((Term.Boolean false))

def __eo_typeof_dt_cons_rec.case_0 : Term -> Datatype -> native_Nat -> Option (Term)
  | T, (Datatype.sum DatatypeCons.unit d), native_nat_zero => some (T)
  | _, _, _ => none

def __eo_typeof_dt_cons_rec.case_1 : Term -> Datatype -> native_Nat -> Option (Term)
  | T, (Datatype.sum (DatatypeCons.cons U c) d), native_nat_zero => some ((Term.DtcAppType U (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero)))
  | _, _, _ => none

def __eo_typeof_dt_cons_rec.case_2 : Term -> Datatype -> native_Nat -> Option (Term)
  | T, (Datatype.sum c d), (native_nat_succ n) => some ((__eo_typeof_dt_cons_rec T d n))
  | _, _, _ => none

def __eo_typeof_dt_sel_return.case_0 : Datatype -> native_Nat -> native_Nat -> Option (Term)
  | (Datatype.sum (DatatypeCons.cons T c) d), native_nat_zero, native_nat_zero => some (T)
  | _, _, _ => none

def __eo_typeof_dt_sel_return.case_1 : Datatype -> native_Nat -> native_Nat -> Option (Term)
  | (Datatype.sum (DatatypeCons.cons T c) d), native_nat_zero, (native_nat_succ m) => some ((__eo_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero m))
  | _, _, _ => none

def __eo_typeof_dt_sel_return.case_2 : Datatype -> native_Nat -> native_Nat -> Option (Term)
  | (Datatype.sum c d), (native_nat_succ n), m => some ((__eo_typeof_dt_sel_return d n m))
  | _, _, _ => none

def __eo_typeof_apply.case_0 : Term -> Term -> Option (Term)
  | (Term.Apply (Term.Apply Term.FunType T) U), V => some ((__eo_requires T V U))
  | _, _ => none

def __eo_typeof_apply.case_1 : Term -> Term -> Option (Term)
  | (Term.DtcAppType T U), V => some ((__eo_requires T V U))
  | _, _ => none

def __eo_typeof_fun_type.case_0 : Term -> Term -> Option (Term)
  | Term.Type, Term.Type => some (Term.Type)
  | _, _ => none

def __eo_lit_type_Numeral.case_0 : Term -> Option (Term)
  | t => some ((Term.UOp UserOp.Int))

def __eo_lit_type_Rational.case_0 : Term -> Option (Term)
  | t => some ((Term.UOp UserOp.Real))

def __eo_lit_type_Binary.case_0 : Term -> Option (Term)
  | t => some ((__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_len t)))

def __eo_lit_type_String.case_0 : Term -> Option (Term)
  | t => some ((Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)))

def __eo_typeof_BitVec.case_0 : Term -> Option (Term)
  | (Term.UOp UserOp.Int) => some (Term.Type)
  | _ => none

def __eo_typeof_Seq.case_0 : Term -> Option (Term)
  | Term.Type => some (Term.Type)
  | _ => none

def __eo_typeof_not.case_0 : Term -> Option (Term)
  | Term.Bool => some (Term.Bool)
  | _ => none

def __eo_typeof_and.case_0 : Term -> Term -> Option (Term)
  | Term.Bool, Term.Bool => some (Term.Bool)
  | _, _ => none

def __eo_typeof_eq.case_0 : Term -> Term -> Option (Term)
  | A, __eo_lv_A_2 => if A = __eo_lv_A_2 then some (Term.Bool) else none

def __eo_typeof.case_0 : Term -> Option (Term)
  | (Term.Boolean b) => some (Term.Bool)
  | _ => none

def __eo_typeof.case_1 : Term -> Option (Term)
  | (Term.Numeral n) => some ((__eo_lit_type_Numeral (Term.Numeral n)))
  | _ => none

def __eo_typeof.case_2 : Term -> Option (Term)
  | (Term.Rational r) => some ((__eo_lit_type_Rational (Term.Rational r)))
  | _ => none

def __eo_typeof.case_3 : Term -> Option (Term)
  | (Term.String s) => some ((__eo_lit_type_String (Term.String s)))
  | _ => none

def __eo_typeof.case_4 : Term -> Option (Term)
  | (Term.Binary w n) => some ((__eo_lit_type_Binary (Term.Binary w n)))
  | _ => none

def __eo_typeof.case_5 : Term -> Option (Term)
  | (Term.Var (Term.String s) T) => some (T)
  | _ => none

def __eo_typeof.case_6 : Term -> Option (Term)
  | (Term.DatatypeType s dd) => some (Term.Type)
  | _ => none

def __eo_typeof.case_7 : Term -> Option (Term)
  | (Term.DtCons s dd i) => some ((__eo_typeof_dt_cons_rec (Term.DatatypeType s dd) (__eo_dd_resolve s dd) i))
  | _ => none

def __eo_typeof.case_8 : Term -> Option (Term)
  | (Term.DtSel s dd i j) => some ((Term.Apply (Term.Apply Term.FunType (Term.DatatypeType s dd)) (__eo_typeof_dt_sel_return (__eo_dd_resolve s dd) i j)))
  | _ => none

def __eo_typeof.case_9 : Term -> Option (Term)
  | (Term.USort i) => some (Term.Type)
  | _ => none

def __eo_typeof.case_10 : Term -> Option (Term)
  | (Term.UConst i T) => some (T)
  | _ => none

def __eo_typeof.case_11 : Term -> Option (Term)
  | Term.Type => some (Term.Type)
  | _ => none

def __eo_typeof.case_12 : Term -> Option (Term)
  | (Term.Apply (Term.Apply Term.FunType __eo_T) __eo_U) => some ((__eo_typeof_fun_type (__eo_typeof __eo_T) (__eo_typeof __eo_U)))
  | _ => none

def __eo_typeof.case_13 : Term -> Option (Term)
  | Term.Bool => some (Term.Type)
  | _ => none

def __eo_typeof.case_14 : Term -> Option (Term)
  | Term.__eo_List => some (Term.Type)
  | _ => none

def __eo_typeof.case_15 : Term -> Option (Term)
  | Term.__eo_List_nil => some (Term.__eo_List)
  | _ => none

def __eo_typeof.case_16 : Term -> Option (Term)
  | (Term.Apply Term.__eo_List_cons __eo_x1) => some ((Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List))
  | _ => none

def __eo_typeof.case_17 : Term -> Option (Term)
  | (Term.UOp UserOp.Int) => some (Term.Type)
  | _ => none

def __eo_typeof.case_18 : Term -> Option (Term)
  | (Term.UOp UserOp.Real) => some (Term.Type)
  | _ => none

def __eo_typeof.case_19 : Term -> Option (Term)
  | (Term.Apply (Term.UOp UserOp.BitVec) __eo_x1) => some ((__eo_typeof_BitVec (__eo_typeof __eo_x1)))
  | _ => none

def __eo_typeof.case_20 : Term -> Option (Term)
  | (Term.UOp UserOp.Char) => some (Term.Type)
  | _ => none

def __eo_typeof.case_21 : Term -> Option (Term)
  | (Term.Apply (Term.UOp UserOp.Seq) __eo_x1) => some ((__eo_typeof_Seq (__eo_typeof __eo_x1)))
  | _ => none

def __eo_typeof.case_22 : Term -> Option (Term)
  | (Term.Apply (Term.UOp UserOp.not) __eo_x1) => some ((__eo_typeof_not (__eo_typeof __eo_x1)))
  | _ => none

def __eo_typeof.case_23 : Term -> Option (Term)
  | (Term.Apply (Term.Apply (Term.UOp UserOp.and) __eo_x1) __eo_x2) => some ((__eo_typeof_and (__eo_typeof __eo_x1) (__eo_typeof __eo_x2)))
  | _ => none

def __eo_typeof.case_24 : Term -> Option (Term)
  | (Term.Apply (Term.Apply (Term.UOp UserOp.imp) __eo_x1) __eo_x2) => some ((__eo_typeof_and (__eo_typeof __eo_x1) (__eo_typeof __eo_x2)))
  | _ => none

def __eo_typeof.case_25 : Term -> Option (Term)
  | (Term.Apply (Term.Apply (Term.UOp UserOp.eq) __eo_x1) __eo_x2) => some ((__eo_typeof_eq (__eo_typeof __eo_x1) (__eo_typeof __eo_x2)))
  | _ => none

def __eo_typeof.case_26 : Term -> Option (Term)
  | (Term.Apply __eo_f __eo_x) => some ((__eo_typeof_apply (__eo_typeof __eo_f) (__eo_typeof __eo_x)))
  | _ => none

def __eo_is_closed_rec.case_0 : Term -> Term -> Option (Term)
  | (Term.Var s T), Term.__eo_List_nil => some ((Term.Boolean false))
  | _, _ => none

def __eo_is_closed_rec.case_1 : Term -> Term -> Option (Term)
  | (Term.Var s T), (Term.Apply (Term.Apply Term.__eo_List_cons x) vs) => some (
    let _v0 := (Term.Var s T)
    (__eo_ite (__eo_eq _v0 x) (Term.Boolean true) (__eo_is_closed_rec _v0 vs)))
  | _, _ => none

def __eo_is_closed_rec.case_2 : Term -> Term -> Option (Term)
  | (Term.Apply f x), env => some ((__eo_and (__eo_is_closed_rec f env) (__eo_is_closed_rec x env)))
  | _, _ => none

def __eo_is_closed_rec.case_3 : Term -> Term -> Option (Term)
  | x, env => some ((Term.Boolean true))

def __eo_is_closed.case_0 : Term -> Option (Term)
  | t => some ((__eo_is_closed_rec t Term.__eo_List_nil))

def __smtx_type_wf_rec.case_0 : SmtType -> Option (native_Bool)
  | SmtType.None => some (false)
  | _ => none

def __smtx_type_wf_rec.case_1 : SmtType -> Option (native_Bool)
  | SmtType.RegLan => some (false)
  | _ => none

def __smtx_type_wf_rec.case_2 : SmtType -> Option (native_Bool)
  | (SmtType.Map x1 x2) => some ((native_and (native_and (__smtx_inhabited_type x1) (__smtx_type_wf_rec x1)) (native_and (__smtx_inhabited_type x2) (__smtx_type_wf_rec x2))))
  | _ => none

def __smtx_type_wf_rec.case_3 : SmtType -> Option (native_Bool)
  | (SmtType.Set x1) => some ((native_and (__smtx_inhabited_type x1) (__smtx_type_wf_rec x1)))
  | _ => none

def __smtx_type_wf_rec.case_4 : SmtType -> Option (native_Bool)
  | (SmtType.Seq x1) => some ((native_and (__smtx_inhabited_type x1) (__smtx_type_wf_rec x1)))
  | _ => none

def __smtx_type_wf_rec.case_5 : SmtType -> Option (native_Bool)
  | (SmtType.Datatype s1 dd2) => some ((native_and (__smtx_dd_has_dt s1 dd2) (__smtx_decl_wf_rec dd2 dd2)))
  | _ => none

def __smtx_type_wf_rec.case_6 : SmtType -> Option (native_Bool)
  | (SmtType.TypeRef s1) => some (false)
  | _ => none

def __smtx_type_wf_rec.case_7 : SmtType -> Option (native_Bool)
  | (SmtType.FunType x1 x2) => some (false)
  | _ => none

def __smtx_type_wf_rec.case_8 : SmtType -> Option (native_Bool)
  | (SmtType.DtcAppType x1 x2) => some (false)
  | _ => none

def __smtx_type_wf_rec.case_9 : SmtType -> Option (native_Bool)
  | U => some (true)

def __smtx_typeof_seq_value.case_0 : SmtSeq -> Option (SmtType)
  | (SmtSeq.cons v vs) => some (
    let _v0 := (__smtx_typeof_seq_value vs)
    (native_ite (native_Teq (SmtType.Seq (__smtx_typeof_value v)) _v0) _v0 SmtType.None))
  | _ => none

def __smtx_typeof_seq_value.case_1 : SmtSeq -> Option (SmtType)
  | (SmtSeq.empty T) => some ((SmtType.Seq T))
  | _ => none

def __smtx_typeof_guard.case_0 : SmtType -> SmtType -> Option (SmtType)
  | T, U => some ((native_ite (native_Teq T SmtType.None) SmtType.None U))

def __smtx_model_eval_not.case_0 : SmtValue -> Option (SmtValue)
  | (SmtValue.Boolean x) => some ((SmtValue.Boolean (native_not x)))
  | _ => none

def __smtx_model_eval_not.case_1 : SmtValue -> Option (SmtValue)
  | t1 => some (SmtValue.NotValue)

def __smtx_model_eval_and.case_0 : SmtValue -> SmtValue -> Option (SmtValue)
  | (SmtValue.Boolean x), (SmtValue.Boolean y) => some ((SmtValue.Boolean (native_and x y)))
  | _, _ => none

def __smtx_model_eval_and.case_1 : SmtValue -> SmtValue -> Option (SmtValue)
  | t1, t2 => some (SmtValue.NotValue)

def __smtx_model_eval_or.case_0 : SmtValue -> SmtValue -> Option (SmtValue)
  | (SmtValue.Boolean x), (SmtValue.Boolean y) => some ((SmtValue.Boolean (native_or x y)))
  | _, _ => none

def __smtx_model_eval_or.case_1 : SmtValue -> SmtValue -> Option (SmtValue)
  | t1, t2 => some (SmtValue.NotValue)

def __smtx_model_eval_imp.case_0 : SmtValue -> SmtValue -> Option (SmtValue)
  | x, y => some ((__smtx_model_eval_or (__smtx_model_eval_not x) y))

def __smtx_typeof_eq.case_0 : SmtType -> SmtType -> Option (SmtType)
  | T, U => some ((__smtx_typeof_guard T (native_ite (native_Teq T U) SmtType.Bool SmtType.None)))

def __smtx_model_eval_eq.case_0 : SmtValue -> SmtValue -> Option (SmtValue)
  | (SmtValue.RegLan r1), (SmtValue.RegLan r2) => some ((SmtValue.Boolean (native_re_ext_eq r1 r2)))
  | _, _ => none

def __smtx_model_eval_eq.case_1 : SmtValue -> SmtValue -> Option (SmtValue)
  | v1, v2 => some ((SmtValue.Boolean (native_veq v1 v2)))

def __smtx_map_get_default.case_0 : SmtMap -> Option (SmtValue)
  | (SmtMap.cons j e m) => some ((__smtx_map_get_default m))
  | _ => none

def __smtx_map_get_default.case_1 : SmtMap -> Option (SmtValue)
  | (SmtMap.default T e) => some (e)
  | _ => none

def __smtx_map_lookup.case_0 : SmtMap -> SmtValue -> Option (SmtValue)
  | (SmtMap.cons j e m), i => some ((native_ite (native_veq j i) e (__smtx_map_lookup m i)))
  | _, _ => none

def __smtx_map_lookup.case_1 : SmtMap -> SmtValue -> Option (SmtValue)
  | (SmtMap.default T e), i => some (e)
  | _, _ => none

def __smtx_typeof_map_value.case_0 : SmtMap -> Option (SmtType)
  | (SmtMap.cons i e m) => some (
    let _v0 := (__smtx_typeof_map_value m)
    (native_ite (native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) _v0) _v0 SmtType.None))
  | _ => none

def __smtx_typeof_map_value.case_1 : SmtMap -> Option (SmtType)
  | (SmtMap.default T e) => some ((SmtType.Map T (__smtx_typeof_value e)))
  | _ => none

def __smtx_map_entries_ordered_after.case_0 : SmtValue -> SmtMap -> Option (native_Bool)
  | i, (SmtMap.cons j e m) => some ((native_vcmp j i))
  | _, _ => none

def __smtx_map_entries_ordered_after.case_1 : SmtValue -> SmtMap -> Option (native_Bool)
  | i, m => some (true)

def __smtx_map_to_set_type.case_0 : SmtType -> Option (SmtType)
  | (SmtType.Map T SmtType.Bool) => some ((SmtType.Set T))
  | _ => none

def __smtx_map_to_set_type.case_1 : SmtType -> Option (SmtType)
  | T => some (SmtType.None)

def __smtx_type_wf_component.case_0 : SmtType -> Option (native_Bool)
  | T => some ((native_and (__smtx_inhabited_type T) (__smtx_type_wf_rec T)))

def __smtx_typeof_apply.case_0 : SmtType -> SmtType -> Option (SmtType)
  | (SmtType.FunType T U), V => some ((__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None)))
  | _, _ => none

def __smtx_typeof_apply.case_1 : SmtType -> SmtType -> Option (SmtType)
  | (SmtType.DtcAppType T U), V => some ((__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None)))
  | _, _ => none

def __smtx_typeof_apply.case_2 : SmtType -> SmtType -> Option (SmtType)
  | T, U => some (SmtType.None)

def __smtx_type_wf.case_0 : SmtType -> Option (native_Bool)
  | SmtType.RegLan => some (true)
  | _ => none

def __smtx_type_wf.case_1 : SmtType -> Option (native_Bool)
  | (SmtType.FunType T U) => some ((native_and (__smtx_type_wf_component T) (__smtx_type_wf U)))
  | _ => none

def __smtx_type_wf.case_2 : SmtType -> Option (native_Bool)
  | T => some ((__smtx_type_wf_component T))

def __smtx_typeof_guard_wf.case_0 : SmtType -> SmtType -> Option (SmtType)
  | T, U => some ((native_ite (__smtx_type_wf T) U SmtType.None))

def __smtx_is_finite_type.case_0 : SmtUSortDom -> SmtType -> Option (native_Bool)
  | uc, T => some ((__smtx_type_bounded uc false T))

def __smtx_apply_head_value.case_0 : SmtValue -> Option (SmtValue)
  | (SmtValue.Apply f a) => some ((__smtx_apply_head_value f))
  | _ => none

def __smtx_apply_head_value.case_1 : SmtValue -> Option (SmtValue)
  | a => some (a)

def __smtx_apply_arg_nth_value.case_0 : SmtValue -> native_Nat -> native_Nat -> Option (SmtValue)
  | (SmtValue.Apply f a), n, (native_nat_succ npos) => some ((native_ite (native_nateq n npos) a (__smtx_apply_arg_nth_value f n npos)))
  | _, _, _ => none

def __smtx_apply_arg_nth_value.case_1 : SmtValue -> native_Nat -> native_Nat -> Option (SmtValue)
  | a, n, npos => some (SmtValue.NotValue)

def __smtx_ret_typeof_sel_rec.case_0 : SmtDatatype -> native_Nat -> native_Nat -> Option (SmtType)
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), native_nat_zero, native_nat_zero => some (T)
  | _, _, _ => none

def __smtx_ret_typeof_sel_rec.case_1 : SmtDatatype -> native_Nat -> native_Nat -> Option (SmtType)
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), native_nat_zero, (native_nat_succ m) => some ((__smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) native_nat_zero m))
  | _, _, _ => none

def __smtx_ret_typeof_sel_rec.case_2 : SmtDatatype -> native_Nat -> native_Nat -> Option (SmtType)
  | (SmtDatatype.sum c d), (native_nat_succ n), m => some ((__smtx_ret_typeof_sel_rec d n m))
  | _, _, _ => none

def __smtx_ret_typeof_sel_rec.case_3 : SmtDatatype -> native_Nat -> native_Nat -> Option (SmtType)
  | d, n, m => some (SmtType.None)

def __smtx_ret_typeof_sel.case_0 : native_String -> SmtDatatypeDecl -> native_Nat -> native_Nat -> Option (SmtType)
  | s, dd, n, m => some ((__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) n m))

def __smtx_dtc_resolve.case_0 : SmtDatatypeCons -> SmtDatatypeDecl -> Option (SmtDatatypeCons)
  | (SmtDatatypeCons.cons (SmtType.TypeRef s) c), dd => some ((SmtDatatypeCons.cons (SmtType.Datatype s dd) (__smtx_dtc_resolve c dd)))
  | _, _ => none

def __smtx_dtc_resolve.case_1 : SmtDatatypeCons -> SmtDatatypeDecl -> Option (SmtDatatypeCons)
  | (SmtDatatypeCons.cons T c), dd => some ((SmtDatatypeCons.cons T (__smtx_dtc_resolve c dd)))
  | _, _ => none

def __smtx_dtc_resolve.case_2 : SmtDatatypeCons -> SmtDatatypeDecl -> Option (SmtDatatypeCons)
  | SmtDatatypeCons.unit, dd => some (SmtDatatypeCons.unit)
  | _, _ => none

def __smtx_dt_resolve.case_0 : SmtDatatype -> SmtDatatypeDecl -> Option (SmtDatatype)
  | (SmtDatatype.sum c d), dd => some ((SmtDatatype.sum (__smtx_dtc_resolve c dd) (__smtx_dt_resolve d dd)))
  | _, _ => none

def __smtx_dt_resolve.case_1 : SmtDatatype -> SmtDatatypeDecl -> Option (SmtDatatype)
  | SmtDatatype.null, dd => some (SmtDatatype.null)
  | _, _ => none

def __smtx_dd_lookup.case_0 : native_String -> SmtDatatypeDecl -> Option (SmtDatatype)
  | s, (SmtDatatypeDecl.cons s2 d dd) => some ((native_ite (native_streq s s2) d (__smtx_dd_lookup s dd)))
  | _, _ => none

def __smtx_dd_lookup.case_1 : native_String -> SmtDatatypeDecl -> Option (SmtDatatype)
  | s, SmtDatatypeDecl.nil => some (SmtDatatype.null)
  | _, _ => none

def __smtx_dd_has_dt.case_0 : native_String -> SmtDatatypeDecl -> Option (native_Bool)
  | s, (SmtDatatypeDecl.cons s2 d dd) => some ((native_or (native_streq s s2) (__smtx_dd_has_dt s dd)))
  | _, _ => none

def __smtx_dd_has_dt.case_1 : native_String -> SmtDatatypeDecl -> Option (native_Bool)
  | s, SmtDatatypeDecl.nil => some (false)
  | _, _ => none

def __smtx_dt_cons_wf_rec.case_0 : SmtDatatypeDecl -> SmtDatatypeCons -> Option (native_Bool)
  | dd, (SmtDatatypeCons.cons (SmtType.TypeRef s) c) => some ((native_and (__smtx_dd_has_dt s dd) (__smtx_dt_cons_wf_rec dd c)))
  | _, _ => none

def __smtx_dt_cons_wf_rec.case_1 : SmtDatatypeDecl -> SmtDatatypeCons -> Option (native_Bool)
  | dd, (SmtDatatypeCons.cons T c) => some ((native_and (native_and (__smtx_inhabited_type T) (__smtx_type_wf_rec T)) (__smtx_dt_cons_wf_rec dd c)))
  | _, _ => none

def __smtx_dt_cons_wf_rec.case_2 : SmtDatatypeDecl -> SmtDatatypeCons -> Option (native_Bool)
  | dd, SmtDatatypeCons.unit => some (true)
  | _, _ => none

def __smtx_dt_wf_rec.case_0 : SmtDatatypeDecl -> SmtDatatype -> Option (native_Bool)
  | dd, (SmtDatatype.sum cF dF) => some ((native_and (__smtx_dt_cons_wf_rec dd cF) (__smtx_dt_wf_rec dd dF)))
  | _, _ => none

def __smtx_dt_wf_rec.case_1 : SmtDatatypeDecl -> SmtDatatype -> Option (native_Bool)
  | dd, SmtDatatype.null => some (true)
  | _, _ => none

def __smtx_decl_wf_rec.case_0 : SmtDatatypeDecl -> SmtDatatypeDecl -> Option (native_Bool)
  | dd, (SmtDatatypeDecl.cons s d ddF) => some ((native_and (__smtx_dt_wf_rec dd d) (native_and (__smtx_inhabited_type (SmtType.Datatype s dd)) (native_and (__smtx_decl_wf_rec dd ddF) (native_not (__smtx_dd_has_dt s ddF))))))
  | _, _ => none

def __smtx_decl_wf_rec.case_1 : SmtDatatypeDecl -> SmtDatatypeDecl -> Option (native_Bool)
  | dd, SmtDatatypeDecl.nil => some (true)
  | _, _ => none

def __smtx_dt_cons_inhabited.case_0 : SmtDatatypeCons -> SmtDatatypeDecl -> Option (native_Bool)
  | (SmtDatatypeCons.cons (SmtType.TypeRef s) c), ddF => some ((native_and (__smtx_decl_inhabited s ddF) (__smtx_dt_cons_inhabited c ddF)))
  | _, _ => none

def __smtx_dt_cons_inhabited.case_1 : SmtDatatypeCons -> SmtDatatypeDecl -> Option (native_Bool)
  | (SmtDatatypeCons.cons T c), ddF => some ((native_and (__smtx_inhabited_type T) (__smtx_dt_cons_inhabited c ddF)))
  | _, _ => none

def __smtx_dt_cons_inhabited.case_2 : SmtDatatypeCons -> SmtDatatypeDecl -> Option (native_Bool)
  | SmtDatatypeCons.unit, ddF => some (true)
  | _, _ => none

def __smtx_dt_inhabited.case_0 : SmtDatatype -> SmtDatatypeDecl -> Option (native_Bool)
  | (SmtDatatype.sum c d), ddF => some ((native_or (__smtx_dt_cons_inhabited c ddF) (__smtx_dt_inhabited d ddF)))
  | _, _ => none

def __smtx_dt_inhabited.case_1 : SmtDatatype -> SmtDatatypeDecl -> Option (native_Bool)
  | SmtDatatype.null, ddF => some (false)
  | _, _ => none

def __smtx_decl_inhabited.case_0 : native_String -> SmtDatatypeDecl -> Option (native_Bool)
  | s, (SmtDatatypeDecl.cons sF dF ddF) => some ((native_ite (native_streq s sF) (__smtx_dt_inhabited dF ddF) (__smtx_decl_inhabited s ddF)))
  | _, _ => none

def __smtx_decl_inhabited.case_1 : native_String -> SmtDatatypeDecl -> Option (native_Bool)
  | s, SmtDatatypeDecl.nil => some (false)
  | _, _ => none

def __smtx_dtc_num_sels.case_0 : SmtDatatypeCons -> Option (native_Nat)
  | (SmtDatatypeCons.cons U c) => some ((native_nat_succ (__smtx_dtc_num_sels c)))
  | _ => none

def __smtx_dtc_num_sels.case_1 : SmtDatatypeCons -> Option (native_Nat)
  | SmtDatatypeCons.unit => some (native_nat_zero)
  | _ => none

def __smtx_dt_num_sels.case_0 : SmtDatatype -> native_Nat -> Option (native_Nat)
  | (SmtDatatype.sum c d), native_nat_zero => some ((__smtx_dtc_num_sels c))
  | _, _ => none

def __smtx_dt_num_sels.case_1 : SmtDatatype -> native_Nat -> Option (native_Nat)
  | (SmtDatatype.sum c d), (native_nat_succ n) => some ((__smtx_dt_num_sels d n))
  | _, _ => none

def __smtx_dt_num_sels.case_2 : SmtDatatype -> native_Nat -> Option (native_Nat)
  | SmtDatatype.null, n => some (native_nat_zero)
  | _, _ => none

def __smtx_typeof_dt_cons_rec.case_0 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, (SmtDatatype.sum SmtDatatypeCons.unit d), native_nat_zero => some (T)
  | _, _, _ => none

def __smtx_typeof_dt_cons_rec.case_1 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), native_nat_zero => some ((SmtType.DtcAppType U (__smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) native_nat_zero)))
  | _, _, _ => none

def __smtx_typeof_dt_cons_rec.case_2 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, (SmtDatatype.sum c d), (native_nat_succ n) => some ((__smtx_typeof_dt_cons_rec T d n))
  | _, _, _ => none

def __smtx_typeof_dt_cons_rec.case_3 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, d, n => some (SmtType.None)

def __smtx_field_type_bounded.case_0 : SmtUSortDom -> native_Bool -> SmtType -> SmtDatatypeDecl -> Option (native_Bool)
  | uc, u, (SmtType.TypeRef s), ddB => some ((__smtx_dd_has_dt s ddB))
  | _, _, _, _ => none

def __smtx_field_type_bounded.case_1 : SmtUSortDom -> native_Bool -> SmtType -> SmtDatatypeDecl -> Option (native_Bool)
  | uc, u, T, ddB => some ((__smtx_type_bounded uc u T))

def __smtx_field_type_default.case_0 : SmtDatatypeDecl -> SmtType -> SmtDatatypeDecl -> Option (SmtValue)
  | dd, (SmtType.TypeRef s), ddF => some ((__smtx_datatype_decl_default s dd ddF))
  | _, _, _ => none

def __smtx_field_type_default.case_1 : SmtDatatypeDecl -> SmtType -> SmtDatatypeDecl -> Option (SmtValue)
  | dd, T, ddF => some ((__smtx_type_default T))

def __smtx_datatype_cons_bounded.case_0 : SmtUSortDom -> native_Bool -> SmtDatatypeCons -> SmtDatatypeDecl -> Option (native_Bool)
  | uc, u, SmtDatatypeCons.unit, ddB => some (true)
  | _, _, _, _ => none

def __smtx_datatype_cons_bounded.case_1 : SmtUSortDom -> native_Bool -> SmtDatatypeCons -> SmtDatatypeDecl -> Option (native_Bool)
  | uc, u, (SmtDatatypeCons.cons T c), ddB => some ((native_and (__smtx_field_type_bounded uc u T ddB) (__smtx_datatype_cons_bounded uc u c ddB)))
  | _, _, _, _ => none

def __smtx_datatype_bounded.case_0 : SmtUSortDom -> native_Bool -> SmtDatatype -> SmtDatatypeDecl -> Option (native_Bool)
  | uc, u, (SmtDatatype.sum c SmtDatatype.null), ddB => some ((__smtx_datatype_cons_bounded uc u c ddB))
  | _, _, _, _ => none

def __smtx_datatype_bounded.case_1 : SmtUSortDom -> native_Bool -> SmtDatatype -> SmtDatatypeDecl -> Option (native_Bool)
  | uc, u, (SmtDatatype.sum c dF), ddB => some ((native_and (native_not u) (native_and (__smtx_datatype_cons_bounded uc u c ddB) (__smtx_datatype_bounded uc u dF ddB))))
  | _, _, _, _ => none

def __smtx_datatype_bounded.case_2 : SmtUSortDom -> native_Bool -> SmtDatatype -> SmtDatatypeDecl -> Option (native_Bool)
  | uc, u, dF, ddB => some ((native_not u))

def __smtx_datatype_decl_bounded_step.case_0 : SmtUSortDom -> native_Bool -> SmtDatatypeDecl -> SmtDatatypeDecl -> Option (SmtDatatypeDecl)
  | uc, u, (SmtDatatypeDecl.cons sF dF ddR), ddB => some ((__smtx_datatype_decl_bounded_step uc u ddR (native_ite (native_and (native_not (__smtx_dd_has_dt sF ddB)) (__smtx_datatype_bounded uc u dF ddB)) (SmtDatatypeDecl.cons sF dF ddB) ddB)))
  | _, _, _, _ => none

def __smtx_datatype_decl_bounded_step.case_1 : SmtUSortDom -> native_Bool -> SmtDatatypeDecl -> SmtDatatypeDecl -> Option (SmtDatatypeDecl)
  | uc, u, SmtDatatypeDecl.nil, ddB => some (ddB)
  | _, _, _, _ => none

def __smtx_datatype_decl_bounded.case_0 : SmtUSortDom -> native_Bool -> SmtDatatypeDecl -> SmtDatatypeDecl -> SmtDatatypeDecl -> Option (SmtDatatypeDecl)
  | uc, u, (SmtDatatypeDecl.cons sC dC ddC), dd, ddB => some ((__smtx_datatype_decl_bounded uc u ddC dd (__smtx_datatype_decl_bounded_step uc u dd ddB)))
  | _, _, _, _, _ => none

def __smtx_datatype_decl_bounded.case_1 : SmtUSortDom -> native_Bool -> SmtDatatypeDecl -> SmtDatatypeDecl -> SmtDatatypeDecl -> Option (SmtDatatypeDecl)
  | uc, u, SmtDatatypeDecl.nil, dd, ddB => some (ddB)
  | _, _, _, _, _ => none

def __smtx_datatype_cons_default.case_0 : SmtValue -> SmtDatatypeDecl -> SmtDatatypeCons -> SmtDatatypeDecl -> Option (SmtValue)
  | v, dd, SmtDatatypeCons.unit, ddF => some (v)
  | _, _, _, _ => none

def __smtx_datatype_cons_default.case_1 : SmtValue -> SmtDatatypeDecl -> SmtDatatypeCons -> SmtDatatypeDecl -> Option (SmtValue)
  | v, dd, (SmtDatatypeCons.cons T c), ddF => some (
    let _v0 := (__smtx_field_type_default dd T ddF)
    (native_ite (native_veq _v0 SmtValue.NotValue) SmtValue.NotValue (__smtx_datatype_cons_default (SmtValue.Apply v _v0) dd c ddF)))
  | _, _, _, _ => none

def __smtx_datatype_default.case_0 : native_String -> SmtDatatypeDecl -> native_Nat -> SmtDatatype -> SmtDatatypeDecl -> Option (SmtValue)
  | s, dd, n, (SmtDatatype.sum cF dF), ddF => some (
    let _v0 := (__smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF)
    (native_ite (native_not (native_veq _v0 SmtValue.NotValue)) _v0 (__smtx_datatype_default s dd (native_nat_succ n) dF ddF)))
  | _, _, _, _, _ => none

def __smtx_datatype_default.case_1 : native_String -> SmtDatatypeDecl -> native_Nat -> SmtDatatype -> SmtDatatypeDecl -> Option (SmtValue)
  | s, dd, n, dF, ddF => some (SmtValue.NotValue)

def __smtx_datatype_decl_default.case_0 : native_String -> SmtDatatypeDecl -> SmtDatatypeDecl -> Option (SmtValue)
  | s, dd, (SmtDatatypeDecl.cons sF dF ddF) => some ((native_ite (native_streq s sF) (__smtx_datatype_default s dd native_nat_zero dF ddF) (__smtx_datatype_decl_default s dd ddF)))
  | _, _, _ => none

def __smtx_datatype_decl_default.case_1 : native_String -> SmtDatatypeDecl -> SmtDatatypeDecl -> Option (SmtValue)
  | s, dd, ddF => some (SmtValue.NotValue)

def __smtx_typeof_dt_cons_value_rec.case_0 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, (SmtDatatype.sum SmtDatatypeCons.unit d), native_nat_zero => some (T)
  | _, _, _ => none

def __smtx_typeof_dt_cons_value_rec.case_1 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), native_nat_zero => some ((SmtType.DtcAppType U (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) native_nat_zero)))
  | _, _, _ => none

def __smtx_typeof_dt_cons_value_rec.case_2 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, (SmtDatatype.sum c d), (native_nat_succ n) => some ((__smtx_typeof_dt_cons_value_rec T d n))
  | _, _, _ => none

def __smtx_typeof_dt_cons_value_rec.case_3 : SmtType -> SmtDatatype -> native_Nat -> Option (SmtType)
  | T, d, n => some (SmtType.None)

def __smtx_typeof_apply_value.case_0 : SmtType -> SmtType -> Option (SmtType)
  | (SmtType.DtcAppType T U), V => some ((__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None)))
  | _, _ => none

def __smtx_typeof_apply_value.case_1 : SmtType -> SmtType -> Option (SmtType)
  | T, U => some (SmtType.None)

def __smtx_typeof_ite.case_0 : SmtType -> SmtType -> SmtType -> Option (SmtType)
  | SmtType.Bool, U, V => some ((native_ite (native_Teq U V) U SmtType.None))
  | _, _, _ => none

def __smtx_typeof_ite.case_1 : SmtType -> SmtType -> SmtType -> Option (SmtType)
  | T, U, V => some (SmtType.None)

def __smtx_model_eval_ite.case_0 : SmtValue -> SmtValue -> SmtValue -> Option (SmtValue)
  | (SmtValue.Boolean true), x, y => some (x)
  | _, _, _ => none

def __smtx_model_eval_ite.case_1 : SmtValue -> SmtValue -> SmtValue -> Option (SmtValue)
  | (SmtValue.Boolean false), x, y => some (y)
  | _, _, _ => none

def __smtx_model_eval_ite.case_2 : SmtValue -> SmtValue -> SmtValue -> Option (SmtValue)
  | t1, t2, t3 => some (SmtValue.NotValue)

def __smtx_typeof_value.case_0 : SmtValue -> Option (SmtType)
  | (SmtValue.Boolean b1) => some (SmtType.Bool)
  | _ => none

def __smtx_typeof_value.case_1 : SmtValue -> Option (SmtType)
  | (SmtValue.Numeral i1) => some (SmtType.Int)
  | _ => none

def __smtx_typeof_value.case_2 : SmtValue -> Option (SmtType)
  | (SmtValue.Real r1) => some (SmtType.Real)
  | _ => none

def __smtx_typeof_value.case_3 : SmtValue -> Option (SmtType)
  | (SmtValue.Binary i1 i2) => some ((native_ite (native_and (native_zleq 0 i1) (native_zeq i2 (native_mod_total i2 (native_int_pow2 i1)))) (SmtType.BitVec (native_int_to_nat i1)) SmtType.None))
  | _ => none

def __smtx_typeof_value.case_4 : SmtValue -> Option (SmtType)
  | (SmtValue.Map m1) => some ((__smtx_typeof_map_value m1))
  | _ => none

def __smtx_typeof_value.case_5 : SmtValue -> Option (SmtType)
  | (SmtValue.Fun e1 T2 T3) => some ((SmtType.FunType T2 T3))
  | _ => none

def __smtx_typeof_value.case_6 : SmtValue -> Option (SmtType)
  | (SmtValue.Set m1) => some ((__smtx_map_to_set_type (__smtx_typeof_map_value m1)))
  | _ => none

def __smtx_typeof_value.case_7 : SmtValue -> Option (SmtType)
  | (SmtValue.Seq q1) => some ((__smtx_typeof_seq_value q1))
  | _ => none

def __smtx_typeof_value.case_8 : SmtValue -> Option (SmtType)
  | (SmtValue.Char c1) => some ((native_ite (native_char_valid c1) SmtType.Char SmtType.None))
  | _ => none

def __smtx_typeof_value.case_9 : SmtValue -> Option (SmtType)
  | (SmtValue.UValue n1 e2) => some ((SmtType.USort n1))
  | _ => none

def __smtx_typeof_value.case_10 : SmtValue -> Option (SmtType)
  | (SmtValue.RegLan re1) => some (SmtType.RegLan)
  | _ => none

def __smtx_typeof_value.case_11 : SmtValue -> Option (SmtType)
  | (SmtValue.DtCons s1 dd2 n3) => some ((__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s1 dd2) (__smtx_dt_resolve (__smtx_dd_lookup s1 dd2) dd2) n3))
  | _ => none

def __smtx_typeof_value.case_12 : SmtValue -> Option (SmtType)
  | (SmtValue.Apply v1 v2) => some ((__smtx_typeof_apply_value (__smtx_typeof_value v1) (__smtx_typeof_value v2)))
  | _ => none

def __smtx_typeof_value.case_13 : SmtValue -> Option (SmtType)
  | v => some (SmtType.None)

def __smtx_model_eval_apply.case_0 : SmtModel -> SmtValue -> SmtValue -> Option (SmtValue)
  | M, v, SmtValue.NotValue => some (SmtValue.NotValue)
  | _, _, _ => none

def __smtx_model_eval_apply.case_1 : SmtModel -> SmtValue -> SmtValue -> Option (SmtValue)
  | M, (SmtValue.DtCons s dd n), i => some ((SmtValue.Apply (SmtValue.DtCons s dd n) i))
  | _, _, _ => none

def __smtx_model_eval_apply.case_2 : SmtModel -> SmtValue -> SmtValue -> Option (SmtValue)
  | M, (SmtValue.Apply f v), i => some ((SmtValue.Apply (SmtValue.Apply f v) i))
  | _, _, _ => none

def __smtx_model_eval_apply.case_3 : SmtModel -> SmtValue -> SmtValue -> Option (SmtValue)
  | M, (SmtValue.Fun e T U), i => some ((native_eval_fun_apply M e T U i))
  | _, _, _ => none

def __smtx_model_eval_apply.case_4 : SmtModel -> SmtValue -> SmtValue -> Option (SmtValue)
  | M, v, i => some (SmtValue.NotValue)

def __smtx_model_eval_dt_sel.case_0 : SmtModel -> native_String -> SmtDatatypeDecl -> native_Nat -> native_Nat -> SmtValue -> Option (SmtValue)
  | M, s, dd, n, m, v => some ((native_ite (native_veq (__smtx_apply_head_value v) (SmtValue.DtCons s dd n)) (__smtx_apply_arg_nth_value v m (__smtx_dt_num_sels (__smtx_dd_lookup s dd) n)) (__smtx_model_eval_apply M (native_model_lookup M (native_wrong_apply_sel_id n m) (SmtType.FunType (SmtType.Datatype s dd) (__smtx_ret_typeof_sel s dd n m))) v)))

def __smtx_model_eval_dt_tester.case_0 : native_String -> SmtDatatypeDecl -> native_Nat -> SmtValue -> Option (SmtValue)
  | s, dd, n, v1 => some ((SmtValue.Boolean (native_veq (__smtx_apply_head_value v1) (SmtValue.DtCons s dd n))))

def __smtx_typeof.case_0 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Boolean b1) => some (SmtType.Bool)
  | _ => none

def __smtx_typeof.case_1 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Numeral i1) => some (SmtType.Int)
  | _ => none

def __smtx_typeof.case_2 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Rational r1) => some (SmtType.Real)
  | _ => none

def __smtx_typeof.case_3 : SmtTerm -> Option (SmtType)
  | (SmtTerm.String s1) => some ((native_ite (native_string_valid s1) (SmtType.Seq SmtType.Char) SmtType.None))
  | _ => none

def __smtx_typeof.case_4 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Binary i1 i2) => some ((native_ite (native_and (native_zleq 0 i1) (native_zeq i2 (native_mod_total i2 (native_int_pow2 i1)))) (SmtType.BitVec (native_int_to_nat i1)) SmtType.None))
  | _ => none

def __smtx_typeof.case_5 : SmtTerm -> Option (SmtType)
  | (SmtTerm.not x1) => some ((native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None))
  | _ => none

def __smtx_typeof.case_6 : SmtTerm -> Option (SmtType)
  | (SmtTerm.and x1 x2) => some ((native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None))
  | _ => none

def __smtx_typeof.case_7 : SmtTerm -> Option (SmtType)
  | (SmtTerm.or x1 x2) => some ((native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None))
  | _ => none

def __smtx_typeof.case_8 : SmtTerm -> Option (SmtType)
  | (SmtTerm.imp x1 x2) => some ((native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None))
  | _ => none

def __smtx_typeof.case_9 : SmtTerm -> Option (SmtType)
  | (SmtTerm.eq x1 x2) => some ((__smtx_typeof_eq (__smtx_typeof x1) (__smtx_typeof x2)))
  | _ => none

def __smtx_typeof.case_10 : SmtTerm -> Option (SmtType)
  | (SmtTerm.ite x1 x2 x3) => some ((__smtx_typeof_ite (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3)))
  | _ => none

def __smtx_typeof.case_11 : SmtTerm -> Option (SmtType)
  | (SmtTerm.DtCons s dd i) => some (
    let _v0 := (SmtType.Datatype s dd)
    (__smtx_typeof_guard_wf _v0 (__smtx_typeof_dt_cons_rec _v0 (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i)))
  | _ => none

def __smtx_typeof.case_12 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Apply (SmtTerm.DtSel s dd i j) x1) => some (
    let _v0 := (__smtx_ret_typeof_sel s dd i j)
    (__smtx_typeof_guard_wf _v0 (__smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s dd) _v0) (__smtx_typeof x1))))
  | _ => none

def __smtx_typeof.case_13 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Apply (SmtTerm.DtTester s dd i) x1) => some (
    let _v0 := (SmtType.Datatype s dd)
    (__smtx_typeof_guard (__smtx_typeof_dt_cons_rec _v0 (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i) (__smtx_typeof_apply (SmtType.FunType _v0 SmtType.Bool) (__smtx_typeof x1))))
  | _ => none

def __smtx_typeof.case_14 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Apply f x1) => some ((__smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x1)))
  | _ => none

def __smtx_typeof.case_15 : SmtTerm -> Option (SmtType)
  | (SmtTerm.Var s T) => some ((__smtx_typeof_guard_wf T T))
  | _ => none

def __smtx_typeof.case_16 : SmtTerm -> Option (SmtType)
  | (SmtTerm.UConst s T) => some ((__smtx_typeof_guard_wf T T))
  | _ => none

def __smtx_typeof.case_17 : SmtTerm -> Option (SmtType)
  | x1 => some (SmtType.None)

def __eo_to_smt_datatype_cons.case_0 : DatatypeCons -> Option (SmtDatatypeCons)
  | DatatypeCons.unit => some (SmtDatatypeCons.unit)
  | _ => none

def __eo_to_smt_datatype_cons.case_1 : DatatypeCons -> Option (SmtDatatypeCons)
  | (DatatypeCons.cons U c) => some ((SmtDatatypeCons.cons (__eo_to_smt_type U) (__eo_to_smt_datatype_cons c)))
  | _ => none

def __eo_to_smt_datatype.case_0 : Datatype -> Option (SmtDatatype)
  | (Datatype.sum c d) => some ((SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d)))
  | _ => none

def __eo_to_smt_datatype.case_1 : Datatype -> Option (SmtDatatype)
  | Datatype.null => some (SmtDatatype.null)
  | _ => none

def __eo_to_smt_datatype_decl.case_0 : DatatypeDecl -> Option (SmtDatatypeDecl)
  | (DatatypeDecl.cons s d dd) => some ((SmtDatatypeDecl.cons s (__eo_to_smt_datatype d) (__eo_to_smt_datatype_decl dd)))
  | _ => none

def __eo_to_smt_datatype_decl.case_1 : DatatypeDecl -> Option (SmtDatatypeDecl)
  | DatatypeDecl.nil => some (SmtDatatypeDecl.nil)
  | _ => none

def __eo_to_smt_reserved_datatype_name.case_0 : native_String -> Option (native_Bool)
  | s => some ((native_string_prefix_eq (native_string_lit "@") s))

def __eo_to_smt_type.case_0 : Term -> Option (SmtType)
  | Term.Bool => some (SmtType.Bool)
  | _ => none

def __eo_to_smt_type.case_1 : Term -> Option (SmtType)
  | (Term.DatatypeType s dd) => some ((native_ite (__eo_to_smt_reserved_datatype_name s) SmtType.None (SmtType.Datatype s (__eo_to_smt_datatype_decl dd))))
  | _ => none

def __eo_to_smt_type.case_2 : Term -> Option (SmtType)
  | (Term.DatatypeTypeRef s) => some ((native_ite (__eo_to_smt_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s)))
  | _ => none

def __eo_to_smt_type.case_3 : Term -> Option (SmtType)
  | (Term.DtcAppType T1 T2) => some (
    let _v0 := (__eo_to_smt_type T2)
    let _v1 := (__eo_to_smt_type T1)
    (__smtx_typeof_guard _v1 (__smtx_typeof_guard _v0 (SmtType.DtcAppType _v1 _v0))))
  | _ => none

def __eo_to_smt_type.case_4 : Term -> Option (SmtType)
  | (Term.USort i) => some ((SmtType.USort i))
  | _ => none

def __eo_to_smt_type.case_5 : Term -> Option (SmtType)
  | (Term.Apply (Term.Apply Term.FunType T1) T2) => some (
    let _v0 := (__eo_to_smt_type T2)
    let _v1 := (__eo_to_smt_type T1)
    (__smtx_typeof_guard _v1 (__smtx_typeof_guard _v0 (SmtType.FunType _v1 _v0))))
  | _ => none

def __eo_to_smt_type.case_6 : Term -> Option (SmtType)
  | (Term.UOp UserOp.Int) => some (SmtType.Int)
  | _ => none

def __eo_to_smt_type.case_7 : Term -> Option (SmtType)
  | (Term.UOp UserOp.Real) => some (SmtType.Real)
  | _ => none

def __eo_to_smt_type.case_8 : Term -> Option (SmtType)
  | (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral x1)) => some ((native_ite (native_zleq 0 x1) (SmtType.BitVec (native_int_to_nat x1)) SmtType.None))
  | _ => none

def __eo_to_smt_type.case_9 : Term -> Option (SmtType)
  | (Term.UOp UserOp.Char) => some (SmtType.Char)
  | _ => none

def __eo_to_smt_type.case_10 : Term -> Option (SmtType)
  | (Term.Apply (Term.UOp UserOp.Seq) x1) => some (
    let _v0 := (__eo_to_smt_type x1)
    (__smtx_typeof_guard _v0 (SmtType.Seq _v0)))
  | _ => none

def __eo_to_smt_type.case_11 : Term -> Option (SmtType)
  | T => some (SmtType.None)

def __eo_to_smt.case_0 : Term -> Option (SmtTerm)
  | (Term.Boolean b) => some ((SmtTerm.Boolean b))
  | _ => none

def __eo_to_smt.case_1 : Term -> Option (SmtTerm)
  | (Term.Numeral n) => some ((SmtTerm.Numeral n))
  | _ => none

def __eo_to_smt.case_2 : Term -> Option (SmtTerm)
  | (Term.Rational r) => some ((SmtTerm.Rational r))
  | _ => none

def __eo_to_smt.case_3 : Term -> Option (SmtTerm)
  | (Term.String s) => some ((SmtTerm.String s))
  | _ => none

def __eo_to_smt.case_4 : Term -> Option (SmtTerm)
  | (Term.Binary w n) => some ((SmtTerm.Binary w n))
  | _ => none

def __eo_to_smt.case_5 : Term -> Option (SmtTerm)
  | (Term.Var (Term.String s) T) => some ((SmtTerm.Var s (__eo_to_smt_type T)))
  | _ => none

def __eo_to_smt.case_6 : Term -> Option (SmtTerm)
  | (Term.DtCons s dd i) => some ((native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None (SmtTerm.DtCons s (__eo_to_smt_datatype_decl dd) i)))
  | _ => none

def __eo_to_smt.case_7 : Term -> Option (SmtTerm)
  | (Term.DtSel s dd i j) => some ((native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None (SmtTerm.DtSel s (__eo_to_smt_datatype_decl dd) i j)))
  | _ => none

def __eo_to_smt.case_8 : Term -> Option (SmtTerm)
  | (Term.UConst i T) => some ((SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)))
  | _ => none

def __eo_to_smt.case_9 : Term -> Option (SmtTerm)
  | (Term.Apply (Term.UOp UserOp.not) x1) => some ((SmtTerm.not (__eo_to_smt x1)))
  | _ => none

def __eo_to_smt.case_10 : Term -> Option (SmtTerm)
  | (Term.Apply (Term.Apply (Term.UOp UserOp.and) x1) x2) => some ((SmtTerm.and (__eo_to_smt x1) (__eo_to_smt x2)))
  | _ => none

def __eo_to_smt.case_11 : Term -> Option (SmtTerm)
  | (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x1) x2) => some ((SmtTerm.imp (__eo_to_smt x1) (__eo_to_smt x2)))
  | _ => none

def __eo_to_smt.case_12 : Term -> Option (SmtTerm)
  | (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) x2) => some ((SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt x2)))
  | _ => none

def __eo_to_smt.case_13 : Term -> Option (SmtTerm)
  | (Term.Apply f y) => some ((SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y)))
  | _ => none

def __eo_to_smt.case_14 : Term -> Option (SmtTerm)
  | y => some (SmtTerm.None)

def __smtx_type_bounded.case_0 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, SmtType.Bool => some ((native_not u))
  | _, _, _ => none

def __smtx_type_bounded.case_1 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, (SmtType.BitVec n1) => some ((native_or (native_not u) (native_nateq n1 native_nat_zero)))
  | _, _, _ => none

def __smtx_type_bounded.case_2 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, (SmtType.Map x1 x2) => some ((native_or (__smtx_type_bounded uc true x2) (native_and (native_not u) (native_and (__smtx_type_bounded uc u x1) (__smtx_type_bounded uc u x2)))))
  | _, _, _ => none

def __smtx_type_bounded.case_3 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, (SmtType.Set x1) => some ((native_and (native_not u) (__smtx_type_bounded uc u x1)))
  | _, _, _ => none

def __smtx_type_bounded.case_4 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, SmtType.Char => some ((native_not u))
  | _, _, _ => none

def __smtx_type_bounded.case_5 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, (SmtType.Datatype s1 dd2) => some ((__smtx_dd_has_dt s1 (__smtx_datatype_decl_bounded uc u dd2 dd2 SmtDatatypeDecl.nil)))
  | _, _, _ => none

def __smtx_type_bounded.case_6 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, (SmtType.USort n1) => some ((native_ite u (native_usort_unit uc n1) (native_usort_finite uc n1)))
  | _, _, _ => none

def __smtx_type_bounded.case_7 : SmtUSortDom -> native_Bool -> SmtType -> Option (native_Bool)
  | uc, u, T => some (false)

def __smtx_type_default.case_0 : SmtType -> Option (SmtValue)
  | SmtType.Bool => some ((SmtValue.Boolean false))
  | _ => none

def __smtx_type_default.case_1 : SmtType -> Option (SmtValue)
  | SmtType.Int => some ((SmtValue.Numeral 0))
  | _ => none

def __smtx_type_default.case_2 : SmtType -> Option (SmtValue)
  | SmtType.Real => some ((SmtValue.Real (native_mk_real 0 1)))
  | _ => none

def __smtx_type_default.case_3 : SmtType -> Option (SmtValue)
  | SmtType.RegLan => some ((SmtValue.RegLan native_re_none))
  | _ => none

def __smtx_type_default.case_4 : SmtType -> Option (SmtValue)
  | (SmtType.BitVec n1) => some ((SmtValue.Binary (native_nat_to_int n1) 0))
  | _ => none

def __smtx_type_default.case_5 : SmtType -> Option (SmtValue)
  | (SmtType.Map x1 x2) => some (
    let _v0 := (__smtx_type_default x2)
    (native_ite (native_veq _v0 SmtValue.NotValue) SmtValue.NotValue (SmtValue.Map (SmtMap.default x1 _v0))))
  | _ => none

def __smtx_type_default.case_6 : SmtType -> Option (SmtValue)
  | (SmtType.Set x1) => some ((SmtValue.Set (SmtMap.default x1 (SmtValue.Boolean false))))
  | _ => none

def __smtx_type_default.case_7 : SmtType -> Option (SmtValue)
  | (SmtType.Seq x1) => some ((SmtValue.Seq (SmtSeq.empty x1)))
  | _ => none

def __smtx_type_default.case_8 : SmtType -> Option (SmtValue)
  | SmtType.Char => some ((SmtValue.Char native_nat_zero))
  | _ => none

def __smtx_type_default.case_9 : SmtType -> Option (SmtValue)
  | (SmtType.Datatype s1 dd2) => some ((__smtx_datatype_decl_default s1 dd2 dd2))
  | _ => none

def __smtx_type_default.case_10 : SmtType -> Option (SmtValue)
  | (SmtType.USort n1) => some ((SmtValue.UValue n1 native_id_zero))
  | _ => none

def __smtx_type_default.case_11 : SmtType -> Option (SmtValue)
  | (SmtType.FunType x1 x2) => some ((SmtValue.Fun native_default_fun_id x1 x2))
  | _ => none

def __smtx_type_default.case_12 : SmtType -> Option (SmtValue)
  | T => some (SmtValue.NotValue)

def __smtx_inhabited_type.case_0 : SmtType -> Option (native_Bool)
  | SmtType.None => some (false)
  | _ => none

def __smtx_inhabited_type.case_1 : SmtType -> Option (native_Bool)
  | (SmtType.Map x1 x2) => some ((__smtx_inhabited_type x2))
  | _ => none

def __smtx_inhabited_type.case_2 : SmtType -> Option (native_Bool)
  | (SmtType.Datatype s1 dd2) => some ((__smtx_decl_inhabited s1 dd2))
  | _ => none

def __smtx_inhabited_type.case_3 : SmtType -> Option (native_Bool)
  | (SmtType.TypeRef s1) => some (false)
  | _ => none

def __smtx_inhabited_type.case_4 : SmtType -> Option (native_Bool)
  | (SmtType.DtcAppType x1 x2) => some (false)
  | _ => none

def __smtx_inhabited_type.case_5 : SmtType -> Option (native_Bool)
  | T => some (true)

def __smtx_seq_canonical.case_0 : SmtUSortDom -> SmtSeq -> Option (native_Bool)
  | uc, (SmtSeq.empty T) => some (true)
  | _, _ => none

def __smtx_seq_canonical.case_1 : SmtUSortDom -> SmtSeq -> Option (native_Bool)
  | uc, (SmtSeq.cons v s) => some ((native_and (__smtx_value_canonical uc v) (__smtx_seq_canonical uc s)))
  | _, _ => none

def __smtx_re_canonical.case_0 : SmtRegLan -> Option (native_Bool)
  | SmtRegLan.empty => some (true)
  | _ => none

def __smtx_re_canonical.case_1 : SmtRegLan -> Option (native_Bool)
  | SmtRegLan.epsilon => some (true)
  | _ => none

def __smtx_re_canonical.case_2 : SmtRegLan -> Option (native_Bool)
  | SmtRegLan.allchar => some (true)
  | _ => none

def __smtx_re_canonical.case_3 : SmtRegLan -> Option (native_Bool)
  | (SmtRegLan.char c) => some ((native_re_elem_valid c))
  | _ => none

def __smtx_re_canonical.case_4 : SmtRegLan -> Option (native_Bool)
  | (SmtRegLan.range lo hi) => some ((native_and (native_re_elem_valid lo) (native_re_elem_valid hi)))
  | _ => none

def __smtx_re_canonical.case_5 : SmtRegLan -> Option (native_Bool)
  | (SmtRegLan.concat r r2) => some ((native_and (__smtx_re_canonical r) (__smtx_re_canonical r2)))
  | _ => none

def __smtx_re_canonical.case_6 : SmtRegLan -> Option (native_Bool)
  | (SmtRegLan.union r r2) => some ((native_and (__smtx_re_canonical r) (__smtx_re_canonical r2)))
  | _ => none

def __smtx_re_canonical.case_7 : SmtRegLan -> Option (native_Bool)
  | (SmtRegLan.inter r r2) => some ((native_and (__smtx_re_canonical r) (__smtx_re_canonical r2)))
  | _ => none

def __smtx_re_canonical.case_8 : SmtRegLan -> Option (native_Bool)
  | (SmtRegLan.star r) => some ((__smtx_re_canonical r))
  | _ => none

def __smtx_re_canonical.case_9 : SmtRegLan -> Option (native_Bool)
  | (SmtRegLan.comp r) => some ((__smtx_re_canonical r))
  | _ => none

def __smtx_map_default_canonical.case_0 : SmtUSortDom -> SmtType -> SmtValue -> Option (native_Bool)
  | uc, T, e => some ((native_ite (__smtx_is_finite_type uc T) (native_veq e (__smtx_type_default (__smtx_typeof_value e))) true))

def __smtx_map_canonical.case_0 : SmtUSortDom -> SmtMap -> Option (native_Bool)
  | uc, (SmtMap.default T e) => some ((native_and (__smtx_map_default_canonical uc T e) (__smtx_value_canonical uc e)))
  | _, _ => none

def __smtx_map_canonical.case_1 : SmtUSortDom -> SmtMap -> Option (native_Bool)
  | uc, (SmtMap.cons i e m) => some ((native_and (native_and (native_and (native_and (__smtx_value_canonical uc i) (__smtx_value_canonical uc e)) (__smtx_map_canonical uc m)) (__smtx_map_entries_ordered_after i m)) (native_not (native_veq e (__smtx_map_get_default m)))))
  | _, _ => none

def __smtx_value_canonical.case_0 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.Binary i1 i2) => some ((native_ite (native_zleq 0 i1) (native_zeq i2 (native_mod_total i2 (native_int_pow2 i1))) true))
  | _, _ => none

def __smtx_value_canonical.case_1 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.Map m1) => some ((__smtx_map_canonical uc m1))
  | _, _ => none

def __smtx_value_canonical.case_2 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.Set m1) => some ((native_and (__smtx_map_canonical uc m1) (native_veq (__smtx_map_get_default m1) (SmtValue.Boolean false))))
  | _, _ => none

def __smtx_value_canonical.case_3 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.Seq q1) => some ((__smtx_seq_canonical uc q1))
  | _, _ => none

def __smtx_value_canonical.case_4 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.Char c1) => some ((native_char_valid c1))
  | _, _ => none

def __smtx_value_canonical.case_5 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.UValue n1 e2) => some ((native_usort_mem uc n1 e2))
  | _, _ => none

def __smtx_value_canonical.case_6 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.RegLan re1) => some ((__smtx_re_canonical re1))
  | _, _ => none

def __smtx_value_canonical.case_7 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, (SmtValue.Apply v1 v2) => some ((native_and (__smtx_value_canonical uc v1) (__smtx_value_canonical uc v2)))
  | _, _ => none

def __smtx_value_canonical.case_8 : SmtUSortDom -> SmtValue -> Option (native_Bool)
  | uc, v => some (true)

def __eo_StateObj_proven.case_0 : CStateObj -> Option (Term)
  | (CStateObj.assume F) => some (F)
  | _ => none

def __eo_StateObj_proven.case_1 : CStateObj -> Option (Term)
  | (CStateObj.assume_push F) => some (F)
  | _ => none

def __eo_StateObj_proven.case_2 : CStateObj -> Option (Term)
  | (CStateObj.proven F) => some (F)
  | _ => none

def __eo_state_proven_nth.case_0 : CState -> native_Int -> Option (Term)
  | (CState.cons so s), 0 => some ((__eo_StateObj_proven so))
  | _, _ => none

def __eo_state_proven_nth.case_1 : CState -> native_Int -> Option (Term)
  | (CState.cons so s), n => some ((__eo_state_proven_nth s (native_zplus n (native_zneg 1))))
  | _, _ => none

def __eo_state_proven_nth.case_2 : CState -> native_Int -> Option (Term)
  | s, n => some ((Term.Boolean true))

def __eo_state_is_closed.case_0 : CState -> Option (native_Bool)
  | (CState.cons (CStateObj.assume_push F) s) => some (false)
  | _ => none

def __eo_state_is_closed.case_1 : CState -> Option (native_Bool)
  | (CState.cons so s) => some ((__eo_state_is_closed s))
  | _ => none

def __eo_state_is_closed.case_2 : CState -> Option (native_Bool)
  | CState.nil => some (true)
  | _ => none

def __eo_state_is_closed.case_3 : CState -> Option (native_Bool)
  | s => some (false)

def __eo_push_assume_check.case_0 : Term -> Term -> CState -> Option (CState)
  | (Term.Boolean true), F, s => some ((CState.cons (CStateObj.assume_push F) s))
  | _, _, _ => none

def __eo_push_assume_check.case_1 : Term -> Term -> CState -> Option (CState)
  | b, F, s => some (CState.Stuck)

def __eo_push_input_assume_check.case_0 : Term -> Term -> CState -> Option (CState)
  | (Term.Boolean true), F, s => some ((CState.cons (CStateObj.assume F) s))
  | _, _, _ => none

def __eo_push_input_assume_check.case_1 : Term -> Term -> CState -> Option (CState)
  | b, F, s => some (CState.Stuck)

def __eo_push_proven_check.case_0 : Term -> Term -> CState -> Option (CState)
  | (Term.Boolean true), F, s => some ((CState.cons (CStateObj.proven F) s))
  | _, _, _ => none

def __eo_push_proven_check.case_1 : Term -> Term -> CState -> Option (CState)
  | b, F, s => some (CState.Stuck)

def __eo_push_proven.case_0 : Term -> CState -> Option (CState)
  | F, s => some ((__eo_push_proven_check (__eo_is_bool_type F) F s))

def __eo_mk_premise_list.case_0 : Term -> CIndexList -> CState -> Option (Term)
  | f, CIndexList.nil, S => some ((__eo_nil f Term.Bool))
  | _, _, _ => none

def __eo_mk_premise_list.case_1 : Term -> CIndexList -> CState -> Option (Term)
  | f, (CIndexList.cons n pl), S => some ((__eo_cons f (__eo_state_proven_nth S n) (__eo_mk_premise_list f pl S)))
  | _, _, _ => none

def __eo_invoke_cmd_check_proven.case_0 : CState -> Term -> Option (CState)
  | (CState.cons (CStateObj.proven F) S), proven => some ((__eo_push_proven_check (__eo_eq F proven) F S))
  | _, _ => none

def __eo_invoke_cmd_check_proven.case_1 : CState -> Term -> Option (CState)
  | S, proven => some (CState.Stuck)

def __eo_cmd_step_proven.case_0 : CState -> CRule -> CArgList -> CIndexList -> Option (Term)
  | S, CRule.contra, CArgList.nil, (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil)) => some ((__eo_prog_contra (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))))
  | _, _, _, _ => none

def __eo_cmd_step_proven.case_1 : CState -> CRule -> CArgList -> CIndexList -> Option (Term)
  | S, CRule.refl, (CArgList.cons a1 CArgList.nil), CIndexList.nil => some ((__eo_prog_refl a1))
  | _, _, _, _ => none

def __eo_cmd_step_proven.case_2 : CState -> CRule -> CArgList -> CIndexList -> Option (Term)
  | S, CRule.symm, CArgList.nil, (CIndexList.cons n1 CIndexList.nil) => some ((__eo_prog_symm (Proof.pf (__eo_state_proven_nth S n1))))
  | _, _, _, _ => none

def __eo_cmd_step_proven.case_3 : CState -> CRule -> CArgList -> CIndexList -> Option (Term)
  | S, CRule.trans, CArgList.nil, premises => some ((__eo_prog_trans (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises S))))
  | _, _, _, _ => none

def __eo_cmd_step_proven.case_4 : CState -> CRule -> CArgList -> CIndexList -> Option (Term)
  | S, r, args, premises => some (Term.Stuck)

def __eo_cmd_step_pop_proven.case_0 : CState -> CRule -> CArgList -> Term -> CIndexList -> Option (Term)
  | S, CRule.scope, CArgList.nil, A, (CIndexList.cons n1 CIndexList.nil) => some ((__eo_prog_scope A (Proof.pf (__eo_state_proven_nth S n1))))
  | _, _, _, _, _ => none

def __eo_cmd_step_pop_proven.case_1 : CState -> CRule -> CArgList -> Term -> CIndexList -> Option (Term)
  | S, r, args, A, premises => some (Term.Stuck)

def __eo_invoke_cmd_step_pop.case_0 : CState -> CState -> CRule -> CArgList -> CIndexList -> Option (CState)
  | s, (CState.cons (CStateObj.assume_push A) s2), r, args, premises => some ((__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) s2))
  | _, _, _, _, _ => none

def __eo_invoke_cmd_step_pop.case_1 : CState -> CState -> CRule -> CArgList -> CIndexList -> Option (CState)
  | s, (CState.cons so s2), r, args, premises => some ((__eo_invoke_cmd_step_pop s s2 r args premises))
  | _, _, _, _, _ => none

def __eo_invoke_cmd_step_pop.case_2 : CState -> CState -> CRule -> CArgList -> CIndexList -> Option (CState)
  | s, s2, r, args, premises => some (CState.Stuck)

def __eo_invoke_cmd.case_0 : CState -> CCmd -> Option (CState)
  | CState.Stuck, c => some (CState.Stuck)
  | _, _ => none

def __eo_invoke_cmd.case_1 : CState -> CCmd -> Option (CState)
  | S, (CCmd.assume_push proven) => some ((__eo_push_assume_check (__eo_and (__eo_is_bool_type proven) (__eo_is_closed proven)) proven S))
  | _, _ => none

def __eo_invoke_cmd.case_2 : CState -> CCmd -> Option (CState)
  | S, (CCmd.check_proven proven) => some ((__eo_invoke_cmd_check_proven S proven))
  | _, _ => none

def __eo_invoke_cmd.case_3 : CState -> CCmd -> Option (CState)
  | S, (CCmd.step r args premises) => some ((__eo_push_proven (__eo_cmd_step_proven S r args premises) S))
  | _, _ => none

def __eo_invoke_cmd.case_4 : CState -> CCmd -> Option (CState)
  | S, (CCmd.step_pop r args premises) => some ((__eo_invoke_cmd_step_pop S S r args premises))
  | _, _ => none

def __eo_invoke_cmd_list.case_0 : CState -> CCmdList -> Option (CState)
  | S, CCmdList.nil => some (S)
  | _, _ => none

def __eo_invoke_cmd_list.case_1 : CState -> CCmdList -> Option (CState)
  | S, (CCmdList.cons c cmds) => some ((__eo_invoke_cmd_list (__eo_invoke_cmd S c) cmds))
  | _, _ => none

def __eo_state_is_refutation.case_0 : CState -> Option (native_Bool)
  | s => some ((__eo_state_is_closed (__eo_invoke_cmd_check_proven s (Term.Boolean false))))

def __eo_invoke_assume_list.case_0 : CState -> CArgList -> Option (CState)
  | S, CArgList.nil => some (S)
  | _, _ => none

def __eo_invoke_assume_list.case_1 : CState -> CArgList -> Option (CState)
  | S, (CArgList.cons F as) => some ((__eo_push_input_assume_check (__eo_and (__eo_is_bool_type F) (__eo_is_closed F)) F (__eo_invoke_assume_list S as)))
  | _, _ => none

def __eo_checker_is_refutation.case_0 : CArgList -> CCmdList -> Option (native_Bool)
  | as, cs => some ((__eo_state_is_refutation (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil as) cs)))


end EoCases
