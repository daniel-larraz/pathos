module
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtEval
import all CpcMini.SmtEval
public import CpcMini.SmtModel
import all CpcMini.SmtModel
public import PathosProofs.Eunoia.Natives

/-!
# The natives of CpcMini are Eunoia's

Written by scripts/natives-layer: for each native that CpcMini's Lean defines
(lean-meta prints it from the same block of Ethos's lean.eos as
Eunoia/Natives.lean has), that it is the same definition (`rfl`). The
generated proofs rewrite the runtime's specs, stated against Eunoia's, by
these. Do not edit.
-/

@[expose] public section

namespace pathos_compiled_checker

/-- `native_Bool` of CpcMini is Eunoia's. -/
theorem Bridge.native_Bool : @SmtEval.native_Bool = @Eunoia.native_Bool := by
  first
    | rfl
    | (simp only [SmtEval.native_Bool, Eunoia.native_Bool]; done)
    | (simp only [SmtEval.native_Bool, Eunoia.native_Bool]; split <;> simp_all)
    | (unfold SmtEval.native_Bool Eunoia.native_Bool; split <;> split <;> simp_all)

/-- `native_Char` of CpcMini is Eunoia's. -/
theorem Bridge.native_Char : @SmtEval.native_Char = @Eunoia.native_Char := by
  first
    | rfl
    | (simp only [SmtEval.native_Char, Eunoia.native_Char]; done)
    | (simp only [SmtEval.native_Char, Eunoia.native_Char]; split <;> simp_all)
    | (unfold SmtEval.native_Char Eunoia.native_Char; split <;> split <;> simp_all)

/-- `native_Int` of CpcMini is Eunoia's. -/
theorem Bridge.native_Int : @SmtEval.native_Int = @Eunoia.native_Int := by
  first
    | rfl
    | (simp only [SmtEval.native_Int, Eunoia.native_Int]; done)
    | (simp only [SmtEval.native_Int, Eunoia.native_Int]; split <;> simp_all)
    | (unfold SmtEval.native_Int Eunoia.native_Int; split <;> split <;> simp_all)

/-- `native_Nat` of CpcMini is Eunoia's. -/
theorem Bridge.native_Nat : @SmtEval.native_Nat = @Eunoia.native_Nat := by
  first
    | rfl
    | (simp only [SmtEval.native_Nat, Eunoia.native_Nat]; done)
    | (simp only [SmtEval.native_Nat, Eunoia.native_Nat]; split <;> simp_all)
    | (unfold SmtEval.native_Nat Eunoia.native_Nat; split <;> split <;> simp_all)

/-- `native_Rat` of CpcMini is Eunoia's. -/
theorem Bridge.native_Rat : @SmtEval.native_Rat = @Eunoia.native_Rat := by
  first
    | rfl
    | (simp only [SmtEval.native_Rat, Eunoia.native_Rat]; done)
    | (simp only [SmtEval.native_Rat, Eunoia.native_Rat]; split <;> simp_all)
    | (unfold SmtEval.native_Rat Eunoia.native_Rat; split <;> split <;> simp_all)

/-- `native_String` of CpcMini is Eunoia's. -/
theorem Bridge.native_String : @SmtEval.native_String = @Eunoia.native_String := by
  first
    | rfl
    | (simp only [SmtEval.native_String, Eunoia.native_String, Bridge.native_Char]; done)
    | (simp only [SmtEval.native_String, Eunoia.native_String, Bridge.native_Char]; split <;> simp_all [Bridge.native_Char])
    | (unfold SmtEval.native_String Eunoia.native_String; split <;> split <;> simp_all [Bridge.native_Char])

/-- `native_and` of CpcMini is Eunoia's. -/
theorem Bridge.native_and : @SmtEval.native_and = @Eunoia.native_and := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_and, Eunoia.native_and, Bridge.native_Bool]; done)
    | (funext x0 x1; simp only [SmtEval.native_and, Eunoia.native_and, Bridge.native_Bool]; split <;> simp_all [Bridge.native_Bool])
    | (funext x0 x1; unfold SmtEval.native_and Eunoia.native_and; split <;> split <;> simp_all [Bridge.native_Bool])

/-- `native_ite` of CpcMini is Eunoia's. -/
theorem Bridge.native_ite : @SmtEval.native_ite = @Eunoia.native_ite := by
  first
    | rfl
    | (funext x0 x1 x2; simp only [SmtEval.native_ite, Eunoia.native_ite, Bridge.native_Bool]; done)
    | (funext x0 x1 x2; simp only [SmtEval.native_ite, Eunoia.native_ite, Bridge.native_Bool]; split <;> simp_all [Bridge.native_Bool])
    | (funext x0 x1 x2; unfold SmtEval.native_ite Eunoia.native_ite; split <;> split <;> simp_all [Bridge.native_Bool])

/-- `native_zeq` of CpcMini is Eunoia's. -/
theorem Bridge.native_zeq : @SmtEval.native_zeq = @Eunoia.native_zeq := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_zeq, Eunoia.native_zeq, Bridge.native_Bool, Bridge.native_Int]; done)
    | (funext x0 x1; simp only [SmtEval.native_zeq, Eunoia.native_zeq, Bridge.native_Bool, Bridge.native_Int]; split <;> simp_all [Bridge.native_Bool, Bridge.native_Int])
    | (funext x0 x1; unfold SmtEval.native_zeq Eunoia.native_zeq; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_Int])

/-- `native_piand` of CpcMini is Eunoia's. -/
theorem Bridge.native_piand : @Eo.native_piand = @Eunoia.native_piand := by
  first
    | rfl
    | (funext x0 x1 x2; simp only [Eo.native_piand, Eunoia.native_piand, Bridge.native_Int]; done)
    | (funext x0 x1 x2; simp only [Eo.native_piand, Eunoia.native_piand, Bridge.native_Int]; split <;> simp_all [Bridge.native_Int])
    | (funext x0 x1 x2; unfold Eo.native_piand Eunoia.native_piand; split <;> split <;> simp_all [Bridge.native_Int])

/-- `native_binary_and` of CpcMini is Eunoia's. -/
theorem Bridge.native_binary_and : @Eo.native_binary_and = @Eunoia.native_binary_and := by
  first
    | rfl
    | (funext x0 x1 x2; simp only [Eo.native_binary_and, Eunoia.native_binary_and, Bridge.native_Int, Bridge.native_ite, Bridge.native_zeq, Bridge.native_piand]; done)
    | (funext x0 x1 x2; simp only [Eo.native_binary_and, Eunoia.native_binary_and, Bridge.native_Int, Bridge.native_ite, Bridge.native_zeq, Bridge.native_piand]; split <;> simp_all [Bridge.native_Int, Bridge.native_ite, Bridge.native_zeq, Bridge.native_piand])
    | (funext x0 x1 x2; unfold Eo.native_binary_and Eunoia.native_binary_and; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_ite, Bridge.native_zeq, Bridge.native_piand])

/-- `native_char_valid` of CpcMini is Eunoia's. -/
theorem Bridge.native_char_valid : @SmtEval.native_char_valid = @Eunoia.native_char_valid := by
  first
    | rfl
    | (funext x0; simp only [SmtEval.native_char_valid, Eunoia.native_char_valid, Bridge.native_Bool, Bridge.native_Char]; done)
    | (funext x0; simp only [SmtEval.native_char_valid, Eunoia.native_char_valid, Bridge.native_Bool, Bridge.native_Char]; split <;> simp_all [Bridge.native_Bool, Bridge.native_Char])
    | (funext x0; unfold SmtEval.native_char_valid Eunoia.native_char_valid; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_Char])

/-- `native_zexp_total` of CpcMini is Eunoia's. -/
theorem Bridge.native_zexp_total : @SmtEval.native_zexp_total = @Eunoia.native_zexp_total := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_zexp_total, Eunoia.native_zexp_total, Bridge.native_Int]; done)
    | (funext x0 x1; simp only [SmtEval.native_zexp_total, Eunoia.native_zexp_total, Bridge.native_Int]; split <;> simp_all [Bridge.native_Int])
    | (funext x0 x1; unfold SmtEval.native_zexp_total Eunoia.native_zexp_total; split <;> split <;> simp_all [Bridge.native_Int])

/-- `native_int_pow2` of CpcMini is Eunoia's. -/
theorem Bridge.native_int_pow2 : @SmtEval.native_int_pow2 = @Eunoia.native_int_pow2 := by
  first
    | rfl
    | (funext x0; simp only [SmtEval.native_int_pow2, Eunoia.native_int_pow2, Bridge.native_Int, Bridge.native_zexp_total]; done)
    | (funext x0; simp only [SmtEval.native_int_pow2, Eunoia.native_int_pow2, Bridge.native_Int, Bridge.native_zexp_total]; split <;> simp_all [Bridge.native_Int, Bridge.native_zexp_total])
    | (funext x0; unfold SmtEval.native_int_pow2 Eunoia.native_int_pow2; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_zexp_total])

/-- `native_int_to_nat` of CpcMini is Eunoia's. -/
theorem Bridge.native_int_to_nat : @SmtEval.native_int_to_nat = @Eunoia.native_int_to_nat := by
  first
    | rfl
    | (funext x0; simp only [SmtEval.native_int_to_nat, Eunoia.native_int_to_nat, Bridge.native_Int, Bridge.native_Nat]; done)
    | (funext x0; simp only [SmtEval.native_int_to_nat, Eunoia.native_int_to_nat, Bridge.native_Int, Bridge.native_Nat]; split <;> simp_all [Bridge.native_Int, Bridge.native_Nat])
    | (funext x0; unfold SmtEval.native_int_to_nat Eunoia.native_int_to_nat; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_Nat])

/-- `native_mk_rational` of CpcMini is Eunoia's. -/
theorem Bridge.native_mk_rational : @SmtEval.native_mk_rational = @Eunoia.native_mk_rational := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_mk_rational, Eunoia.native_mk_rational, Bridge.native_Int, Bridge.native_Rat]; done)
    | (funext x0 x1; simp only [SmtEval.native_mk_rational, Eunoia.native_mk_rational, Bridge.native_Int, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Int, Bridge.native_Rat])
    | (funext x0 x1; unfold SmtEval.native_mk_rational Eunoia.native_mk_rational; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_Rat])

/-- `native_mod_total` of CpcMini is Eunoia's. -/
theorem Bridge.native_mod_total : @SmtEval.native_mod_total = @Eunoia.native_mod_total := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_mod_total, Eunoia.native_mod_total, Bridge.native_Int]; done)
    | (funext x0 x1; simp only [SmtEval.native_mod_total, Eunoia.native_mod_total, Bridge.native_Int]; split <;> simp_all [Bridge.native_Int])
    | (funext x0 x1; unfold SmtEval.native_mod_total Eunoia.native_mod_total; split <;> split <;> simp_all [Bridge.native_Int])

/-- `native_nat_to_int` of CpcMini is Eunoia's. -/
theorem Bridge.native_nat_to_int : @Smtm.native_nat_to_int = @Eunoia.native_nat_to_int := by
  first
    | rfl
    | (funext x0; simp only [Smtm.native_nat_to_int, Eunoia.native_nat_to_int, Bridge.native_Int, Bridge.native_Nat]; done)
    | (funext x0; simp only [Smtm.native_nat_to_int, Eunoia.native_nat_to_int, Bridge.native_Int, Bridge.native_Nat]; split <;> simp_all [Bridge.native_Int, Bridge.native_Nat])
    | (funext x0; unfold Smtm.native_nat_to_int Eunoia.native_nat_to_int; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_Nat])

/-- `native_nateq` of CpcMini is Eunoia's. -/
theorem Bridge.native_nateq : @Smtm.native_nateq = @Eunoia.native_nateq := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_nateq, Eunoia.native_nateq, Bridge.native_Bool, Bridge.native_Nat]; done)
    | (funext x0 x1; simp only [Smtm.native_nateq, Eunoia.native_nateq, Bridge.native_Bool, Bridge.native_Nat]; split <;> simp_all [Bridge.native_Bool, Bridge.native_Nat])
    | (funext x0 x1; unfold Smtm.native_nateq Eunoia.native_nateq; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_Nat])

/-- `native_natlt` of CpcMini is Eunoia's. -/
theorem Bridge.native_natlt : @Smtm.native_natlt = @Eunoia.native_natlt := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_natlt, Eunoia.native_natlt, Bridge.native_Bool, Bridge.native_Nat]; done)
    | (funext x0 x1; simp only [Smtm.native_natlt, Eunoia.native_natlt, Bridge.native_Bool, Bridge.native_Nat]; split <;> simp_all [Bridge.native_Bool, Bridge.native_Nat])
    | (funext x0 x1; unfold Smtm.native_natlt Eunoia.native_natlt; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_Nat])

/-- `native_not` of CpcMini is Eunoia's. -/
theorem Bridge.native_not : @SmtEval.native_not = @Eunoia.native_not := by
  first
    | rfl
    | (funext x0; simp only [SmtEval.native_not, Eunoia.native_not, Bridge.native_Bool]; done)
    | (funext x0; simp only [SmtEval.native_not, Eunoia.native_not, Bridge.native_Bool]; split <;> simp_all [Bridge.native_Bool])
    | (funext x0; unfold SmtEval.native_not Eunoia.native_not; split <;> split <;> simp_all [Bridge.native_Bool])

/-- `native_or` of CpcMini is Eunoia's. -/
theorem Bridge.native_or : @SmtEval.native_or = @Eunoia.native_or := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_or, Eunoia.native_or, Bridge.native_Bool]; done)
    | (funext x0 x1; simp only [SmtEval.native_or, Eunoia.native_or, Bridge.native_Bool]; split <;> simp_all [Bridge.native_Bool])
    | (funext x0 x1; unfold SmtEval.native_or Eunoia.native_or; split <;> split <;> simp_all [Bridge.native_Bool])

/-- `native_qabs` of CpcMini is Eunoia's. -/
theorem Bridge.native_qabs : @Smtm.native_qabs = @Eunoia.native_qabs := by
  first
    | rfl
    | (funext x0; simp only [Smtm.native_qabs, Eunoia.native_qabs, Bridge.native_Rat]; done)
    | (funext x0; simp only [Smtm.native_qabs, Eunoia.native_qabs, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Rat])
    | (funext x0; unfold Smtm.native_qabs Eunoia.native_qabs; split <;> split <;> simp_all [Bridge.native_Rat])

/-- `native_qdiv_total` of CpcMini is Eunoia's. -/
theorem Bridge.native_qdiv_total : @Smtm.native_qdiv_total = @Eunoia.native_qdiv_total := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_qdiv_total, Eunoia.native_qdiv_total, Bridge.native_Rat]; done)
    | (funext x0 x1; simp only [Smtm.native_qdiv_total, Eunoia.native_qdiv_total, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Rat])
    | (funext x0 x1; unfold Smtm.native_qdiv_total Eunoia.native_qdiv_total; split <;> split <;> simp_all [Bridge.native_Rat])

/-- `native_qleq` of CpcMini is Eunoia's. -/
theorem Bridge.native_qleq : @Smtm.native_qleq = @Eunoia.native_qleq := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_qleq, Eunoia.native_qleq, Bridge.native_Bool, Bridge.native_Rat]; done)
    | (funext x0 x1; simp only [Smtm.native_qleq, Eunoia.native_qleq, Bridge.native_Bool, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Bool, Bridge.native_Rat])
    | (funext x0 x1; unfold Smtm.native_qleq Eunoia.native_qleq; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_Rat])

/-- `native_qlt` of CpcMini is Eunoia's. -/
theorem Bridge.native_qlt : @Smtm.native_qlt = @Eunoia.native_qlt := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_qlt, Eunoia.native_qlt, Bridge.native_Bool, Bridge.native_Rat]; done)
    | (funext x0 x1; simp only [Smtm.native_qlt, Eunoia.native_qlt, Bridge.native_Bool, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Bool, Bridge.native_Rat])
    | (funext x0 x1; unfold Smtm.native_qlt Eunoia.native_qlt; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_Rat])

/-- `native_qmult` of CpcMini is Eunoia's. -/
theorem Bridge.native_qmult : @Smtm.native_qmult = @Eunoia.native_qmult := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_qmult, Eunoia.native_qmult, Bridge.native_Rat]; done)
    | (funext x0 x1; simp only [Smtm.native_qmult, Eunoia.native_qmult, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Rat])
    | (funext x0 x1; unfold Smtm.native_qmult Eunoia.native_qmult; split <;> split <;> simp_all [Bridge.native_Rat])

/-- `native_qneg` of CpcMini is Eunoia's. -/
theorem Bridge.native_qneg : @Smtm.native_qneg = @Eunoia.native_qneg := by
  first
    | rfl
    | (funext x0; simp only [Smtm.native_qneg, Eunoia.native_qneg, Bridge.native_Rat]; done)
    | (funext x0; simp only [Smtm.native_qneg, Eunoia.native_qneg, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Rat])
    | (funext x0; unfold Smtm.native_qneg Eunoia.native_qneg; split <;> split <;> simp_all [Bridge.native_Rat])

/-- `native_qplus` of CpcMini is Eunoia's. -/
theorem Bridge.native_qplus : @Smtm.native_qplus = @Eunoia.native_qplus := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_qplus, Eunoia.native_qplus, Bridge.native_Rat]; done)
    | (funext x0 x1; simp only [Smtm.native_qplus, Eunoia.native_qplus, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Rat])
    | (funext x0 x1; unfold Smtm.native_qplus Eunoia.native_qplus; split <;> split <;> simp_all [Bridge.native_Rat])

/-- `native_str_len` of CpcMini is Eunoia's. -/
theorem Bridge.native_str_len : @Eo.native_str_len = @Eunoia.native_str_len := by
  first
    | rfl
    | (funext x0; simp only [Eo.native_str_len, Eunoia.native_str_len, Bridge.native_Int, Bridge.native_String]; done)
    | (funext x0; simp only [Eo.native_str_len, Eunoia.native_str_len, Bridge.native_Int, Bridge.native_String]; split <;> simp_all [Bridge.native_Int, Bridge.native_String])
    | (funext x0; unfold Eo.native_str_len Eunoia.native_str_len; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_String])

/-- `native_streq` of CpcMini is Eunoia's. -/
theorem Bridge.native_streq : @SmtEval.native_streq = @Eunoia.native_streq := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_streq, Eunoia.native_streq, Bridge.native_Bool, Bridge.native_String]; done)
    | (funext x0 x1; simp only [SmtEval.native_streq, Eunoia.native_streq, Bridge.native_Bool, Bridge.native_String]; split <;> simp_all [Bridge.native_Bool, Bridge.native_String])
    | (funext x0 x1; unfold SmtEval.native_streq Eunoia.native_streq; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_String])

/-- `native_string_lit` of CpcMini is Eunoia's. -/
theorem Bridge.native_string_lit : @SmtEval.native_string_lit = @Eunoia.native_string_lit := by
  first
    | rfl
    | (funext x0; simp only [SmtEval.native_string_lit, Eunoia.native_string_lit, Bridge.native_String]; done)
    | (funext x0; simp only [SmtEval.native_string_lit, Eunoia.native_string_lit, Bridge.native_String]; split <;> simp_all [Bridge.native_String])
    | (funext x0; unfold SmtEval.native_string_lit Eunoia.native_string_lit; split <;> split <;> simp_all [Bridge.native_String])

/-- `native_string_prefix_eq` of CpcMini is Eunoia's. -/
theorem Bridge.native_string_prefix_eq : @Smtm.native_string_prefix_eq = @Eunoia.native_string_prefix_eq := by
  funext x0 x1
  fun_induction Eunoia.native_string_prefix_eq x0 x1 <;>
    simp_all [Smtm.native_string_prefix_eq, Eunoia.native_string_prefix_eq, Bridge.native_Bool, Bridge.native_String]

/-- `native_string_valid` of CpcMini is Eunoia's. -/
theorem Bridge.native_string_valid : @SmtEval.native_string_valid = @Eunoia.native_string_valid := by
  first
    | rfl
    | (funext x0; simp only [SmtEval.native_string_valid, Eunoia.native_string_valid, Bridge.native_Bool, Bridge.native_String, Bridge.native_char_valid]; done)
    | (funext x0; simp only [SmtEval.native_string_valid, Eunoia.native_string_valid, Bridge.native_Bool, Bridge.native_String, Bridge.native_char_valid]; split <;> simp_all [Bridge.native_Bool, Bridge.native_String, Bridge.native_char_valid])
    | (funext x0; unfold SmtEval.native_string_valid Eunoia.native_string_valid; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_String, Bridge.native_char_valid])

/-- `native_to_int` of CpcMini is Eunoia's. -/
theorem Bridge.native_to_int : @Smtm.native_to_int = @Eunoia.native_to_int := by
  first
    | rfl
    | (funext x0; simp only [Smtm.native_to_int, Eunoia.native_to_int, Bridge.native_Int, Bridge.native_Rat]; done)
    | (funext x0; simp only [Smtm.native_to_int, Eunoia.native_to_int, Bridge.native_Int, Bridge.native_Rat]; split <;> simp_all [Bridge.native_Int, Bridge.native_Rat])
    | (funext x0; unfold Smtm.native_to_int Eunoia.native_to_int; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_Rat])

/-- `native_to_real` of CpcMini is Eunoia's. -/
theorem Bridge.native_to_real : @Smtm.native_to_real = @Eunoia.native_to_real := by
  first
    | rfl
    | (funext x0; simp only [Smtm.native_to_real, Eunoia.native_to_real, Bridge.native_Int, Bridge.native_Rat, Bridge.native_mk_rational]; done)
    | (funext x0; simp only [Smtm.native_to_real, Eunoia.native_to_real, Bridge.native_Int, Bridge.native_Rat, Bridge.native_mk_rational]; split <;> simp_all [Bridge.native_Int, Bridge.native_Rat, Bridge.native_mk_rational])
    | (funext x0; unfold Smtm.native_to_real Eunoia.native_to_real; split <;> split <;> simp_all [Bridge.native_Int, Bridge.native_Rat, Bridge.native_mk_rational])

/-- `native_uconst_id` of CpcMini is Eunoia's. -/
theorem Bridge.native_uconst_id : @Smtm.native_uconst_id = @Eunoia.native_uconst_id := by
  first
    | rfl
    | (funext x0; simp only [Smtm.native_uconst_id, Eunoia.native_uconst_id, Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit]; done)
    | (funext x0; simp only [Smtm.native_uconst_id, Eunoia.native_uconst_id, Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit]; split <;> simp_all [Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit])
    | (funext x0; unfold Smtm.native_uconst_id Eunoia.native_uconst_id; split <;> split <;> simp_all [Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit])

/-- `native_wrong_apply_sel_id` of CpcMini is Eunoia's. -/
theorem Bridge.native_wrong_apply_sel_id : @Smtm.native_wrong_apply_sel_id = @Eunoia.native_wrong_apply_sel_id := by
  first
    | rfl
    | (funext x0 x1; simp only [Smtm.native_wrong_apply_sel_id, Eunoia.native_wrong_apply_sel_id, Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit]; done)
    | (funext x0 x1; simp only [Smtm.native_wrong_apply_sel_id, Eunoia.native_wrong_apply_sel_id, Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit]; split <;> simp_all [Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit])
    | (funext x0 x1; unfold Smtm.native_wrong_apply_sel_id Eunoia.native_wrong_apply_sel_id; split <;> split <;> simp_all [Bridge.native_Nat, Bridge.native_String, Bridge.native_string_lit])

/-- `native_zleq` of CpcMini is Eunoia's. -/
theorem Bridge.native_zleq : @SmtEval.native_zleq = @Eunoia.native_zleq := by
  first
    | rfl
    | (funext x0 x1; simp only [SmtEval.native_zleq, Eunoia.native_zleq, Bridge.native_Bool, Bridge.native_Int]; done)
    | (funext x0 x1; simp only [SmtEval.native_zleq, Eunoia.native_zleq, Bridge.native_Bool, Bridge.native_Int]; split <;> simp_all [Bridge.native_Bool, Bridge.native_Int])
    | (funext x0 x1; unfold SmtEval.native_zleq Eunoia.native_zleq; split <;> split <;> simp_all [Bridge.native_Bool, Bridge.native_Int])

/-- `native_zneg` of CpcMini is Eunoia's. -/
theorem Bridge.native_zneg : @Eo.native_zneg = @Eunoia.native_zneg := by
  first
    | rfl
    | (funext x0; simp only [Eo.native_zneg, Eunoia.native_zneg, Bridge.native_Int]; done)
    | (funext x0; simp only [Eo.native_zneg, Eunoia.native_zneg, Bridge.native_Int]; split <;> simp_all [Bridge.native_Int])
    | (funext x0; unfold Eo.native_zneg Eunoia.native_zneg; split <;> split <;> simp_all [Bridge.native_Int])

/-- `native_zplus` of CpcMini is Eunoia's. -/
theorem Bridge.native_zplus : @Eo.native_zplus = @Eunoia.native_zplus := by
  first
    | rfl
    | (funext x0 x1; simp only [Eo.native_zplus, Eunoia.native_zplus, Bridge.native_Int]; done)
    | (funext x0 x1; simp only [Eo.native_zplus, Eunoia.native_zplus, Bridge.native_Int]; split <;> simp_all [Bridge.native_Int])
    | (funext x0 x1; unfold Eo.native_zplus Eunoia.native_zplus; split <;> split <;> simp_all [Bridge.native_Int])

end pathos_compiled_checker
