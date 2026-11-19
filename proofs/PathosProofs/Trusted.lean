module
public import MiniChecker
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Int.Bitwise

/-!
# What the proofs trust about the checker's Rust

Charon and Aeneas translate all of the compiled checker except two modules,
which they leave as axioms without a meaning: `num.rs`, the integers and
rationals over `malachite`, and the functions of `front.rs` that work on
text. This file says what those functions compute. Every statement here is
an **axiom**: nothing checks it against the Rust. It is, with Lean's own
axioms and logos's, everything that a theorem of `PathosProofs` rests on
beyond what Charon and Aeneas did (`scripts/proofs-axioms` checks that).

How to read it against `generated/cpcmini-checker/src/num.rs`:

* `num.Integer` is the mathematical integers and `num.Rational` the
  rationals: `toInt`/`ofInt` and `toRat`/`ofRat` are inverse to each other.
  This says that a value of the Rust type is determined by the number it
  stands for, and that every number has one. (`malachite` keeps integers
  and rationals in one normal form; a rational is always in lowest terms.)
* Each function returns `ok`: it does not panic and it ends. For the
  functions that take an exponent or a shift this ignores running out of
  memory, which ends the process rather than giving a wrong answer.
* Where the Rust documents a precondition (`y` must be non-zero), the
  axiom has it as a hypothesis and nothing is said without it.
* `hash_code` is only said to return: a Lean function gives equal results
  on equal arguments, which is all that the table of terms needs.
* Nothing is said about the functions that print (`Debug`, `Display`),
  which no checking function calls, nor about `MaybeUninit` and `!=` on
  `bool`, which Aeneas declares and nothing uses.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

namespace num

/-! ## The numbers -/

/-- The integer a value of the Rust type stands for. -/
axiom Integer.toInt : Integer → Int
/-- The value of the Rust type for an integer. -/
axiom Integer.ofInt : Int → Integer
axiom Integer.toInt_ofInt (z : Int) : (Integer.ofInt z).toInt = z
axiom Integer.ofInt_toInt (a : Integer) : Integer.ofInt a.toInt = a

/-- The rational a value of the Rust type stands for. -/
axiom Rational.toRat : Rational → ℚ
/-- The value of the Rust type for a rational. -/
axiom Rational.ofRat : ℚ → Rational
axiom Rational.toRat_ofRat (q : ℚ) : (Rational.ofRat q).toRat = q
axiom Rational.ofRat_toRat (a : Rational) : Rational.ofRat a.toRat = a

/-! ## `Integer` -/

axiom Integer.clone_spec (a : Integer) :
  Integer.Insts.CoreCloneClone.clone a = ok a

axiom Integer.eq_spec (a b : Integer) :
  Integer.Insts.CoreCmpPartialEqInteger.eq a b = ok (decide (a.toInt = b.toInt))

axiom Integer.partial_cmp_spec (a b : Integer) :
  Integer.Insts.CoreCmpPartialOrdInteger.partial_cmp a b
    = ok (some (compare a.toInt b.toInt))

axiom Integer.cmp_spec (a b : Integer) :
  Integer.Insts.CoreCmpOrd.cmp a b = ok (compare a.toInt b.toInt)

axiom Integer.hash_code_spec (a : Integer) : ∃ h, Integer.hash_code a = ok h

axiom Integer.zero_spec : Integer.zero = ok (Integer.ofInt 0)
axiom Integer.one_spec : Integer.one = ok (Integer.ofInt 1)

axiom Integer.from_u32_spec (v : Std.U32) :
  Integer.Insts.CoreConvertFromU32.from v = ok (Integer.ofInt v.val)

axiom Integer.from_usize_spec (v : Std.Usize) :
  Integer.Insts.CoreConvertFromUsize.from v = ok (Integer.ofInt v.val)

/-- The sign: -1, 0 or 1. -/
axiom Integer.sgn_spec (a : Integer) :
  ∃ r : Std.I32, Integer.sgn a = ok r ∧ r.val = Int.sign a.toInt

axiom Integer.neg_spec (a : Integer) :
  Integer.neg a = ok (Integer.ofInt (-a.toInt))

axiom Integer.add_spec (a b : Integer) :
  Integer.add a b = ok (Integer.ofInt (a.toInt + b.toInt))

axiom Integer.mul_spec (a b : Integer) :
  Integer.mul a b = ok (Integer.ofInt (a.toInt * b.toInt))

axiom Integer.pow_spec (a : Integer) (n : Std.U32) :
  Integer.pow a n = ok (Integer.ofInt (a.toInt ^ n.val))

/-- The bitwise operations are those of two's complement with infinitely
many sign bits, as `mpz_ior`, `mpz_and`, `mpz_xor` and `mpz_com`. -/
axiom Integer.bitwise_or_spec (a b : Integer) :
  Integer.bitwise_or a b = ok (Integer.ofInt (Int.lor a.toInt b.toInt))

axiom Integer.bitwise_and_spec (a b : Integer) :
  Integer.bitwise_and a b = ok (Integer.ofInt (Int.land a.toInt b.toInt))

axiom Integer.bitwise_xor_spec (a b : Integer) :
  Integer.bitwise_xor a b = ok (Integer.ofInt (Int.xor a.toInt b.toInt))

axiom Integer.bitwise_not_spec (a : Integer) :
  Integer.bitwise_not a = ok (Integer.ofInt (-a.toInt - 1))

axiom Integer.multiply_by_pow2_spec (a : Integer) (n : Std.U32) :
  Integer.multiply_by_pow2 a n = ok (Integer.ofInt (a.toInt * 2 ^ n.val))

/-- The remainder of the floor division by `2^n`; never negative. -/
axiom Integer.mod_by_pow2_spec (a : Integer) (n : Std.U32) :
  Integer.mod_by_pow2 a n = ok (Integer.ofInt (Int.emod a.toInt (2 ^ n.val)))

/-- Bits `low .. low + count` of the value, as a non-negative integer. -/
axiom Integer.extract_bit_range_spec (a : Integer) (count low : Std.U32) :
  Integer.extract_bit_range a count low
    = ok (Integer.ofInt
        (Int.ediv (Int.emod a.toInt (2 ^ (low.val + count.val))) (2 ^ low.val)))

/-- `2^amount - 1` shifted left by `size`, or-ed into the value. -/
axiom Integer.one_extend_spec (a : Integer) (size amount : Std.U32) :
  Integer.one_extend a size amount
    = ok (Integer.ofInt (Int.lor a.toInt ((2 ^ amount.val - 1) * 2 ^ size.val)))

/-- The quotient rounded towards negative infinity. -/
axiom Integer.floor_div_quotient_spec (a b : Integer) (h : b.toInt ≠ 0) :
  Integer.floor_div_quotient a b = ok (Integer.ofInt (Int.fdiv a.toInt b.toInt))

/-- The remainder of that division; it has the sign of the divisor. -/
axiom Integer.floor_div_remainder_spec (a b : Integer) (h : b.toInt ≠ 0) :
  Integer.floor_div_remainder a b = ok (Integer.ofInt (Int.fmod a.toInt b.toInt))

/-- Euclidean division: the remainder is never negative. -/
axiom Integer.euclidean_qr_spec (a b : Integer) (h : b.toInt ≠ 0) :
  Integer.euclidean_qr a b
    = ok (Integer.ofInt (Int.ediv a.toInt b.toInt),
          Integer.ofInt (Int.emod a.toInt b.toInt))

axiom Integer.fits_u32_spec (a : Integer) :
  Integer.fits_u32 a = ok (decide (0 ≤ a.toInt ∧ a.toInt < 2 ^ 32))

/-- The value as a `u32`; 0 when it is not one. -/
axiom Integer.to_u32_spec (a : Integer) :
  ∃ r : Std.U32, Integer.to_u32 a = ok r ∧
    (r.val : Int) = if 0 ≤ a.toInt ∧ a.toInt < 2 ^ 32 then a.toInt else 0

/-! ## `Rational` -/

axiom Rational.clone_spec (a : Rational) :
  Rational.Insts.CoreCloneClone.clone a = ok a

axiom Rational.eq_spec (a b : Rational) :
  Rational.Insts.CoreCmpPartialEqRational.eq a b = ok (decide (a.toRat = b.toRat))

axiom Rational.partial_cmp_spec (a b : Rational) :
  Rational.Insts.CoreCmpPartialOrdRational.partial_cmp a b
    = ok (some (compare a.toRat b.toRat))

axiom Rational.hash_code_spec (a : Rational) : ∃ h, Rational.hash_code a = ok h

/-- `n / d`, or `None` when `d` is zero. -/
axiom Rational.from_integers_spec (n d : Integer) :
  Rational.from_integers n d
    = ok (if d.toInt = 0 then none
          else some (Rational.ofRat ((n.toInt : ℚ) / (d.toInt : ℚ))))

axiom Rational.from_integer_spec (n : Integer) :
  Rational.from_integer n = ok (Rational.ofRat (n.toInt : ℚ))

/-- The numerator of the number in lowest terms, with its sign. -/
axiom Rational.numerator_spec (a : Rational) :
  Rational.numerator a = ok (Integer.ofInt a.toRat.num)

/-- The denominator of the number in lowest terms, which is positive. -/
axiom Rational.denominator_spec (a : Rational) :
  Rational.denominator a = ok (Integer.ofInt (a.toRat.den : Int))

axiom Rational.sgn_spec (a : Rational) :
  ∃ r : Std.I32, Rational.sgn a = ok r ∧ r.val = Int.sign a.toRat.num

axiom Rational.floor_spec (a : Rational) :
  Rational.floor a = ok (Integer.ofInt (Rat.floor a.toRat))

axiom Rational.neg_spec (a : Rational) :
  Rational.neg a = ok (Rational.ofRat (-a.toRat))

axiom Rational.add_spec (a b : Rational) :
  Rational.add a b = ok (Rational.ofRat (a.toRat + b.toRat))

axiom Rational.mul_spec (a b : Rational) :
  Rational.mul a b = ok (Rational.ofRat (a.toRat * b.toRat))

axiom Rational.div_spec (a b : Rational) (h : b.toRat ≠ 0) :
  Rational.div a b = ok (Rational.ofRat (a.toRat / b.toRat))

axiom Rational.pow_spec (a : Rational) (n : Std.U32) :
  Rational.pow a n = ok (Rational.ofRat (a.toRat ^ n.val))

end num

/-! ## The text functions

`front.rs` holds what works on text, for the program around the checker.
The checking code calls four of its functions. Two read the numerals
written in the generated code (`parse_int`, `parse_rat`); the checker for
CpcMini has none, so they are not declared here. The other two:

* `native_literal code` is the constant that the EO definitions write as
  the text number `code` of the generated list `NATIVE_TEXTS`
  (`src/names.rs`).
* `constant_name uninterpreted n` is the text `@u.n` or `@c.n`.

Of both only this is assumed so far: they return. What each returns is a
statement about one signature's list of texts and about the printing of
integers; none of the proofs here needs it yet.
-/

axiom front.native_literal_spec (code : Std.U32) :
  ∃ r, front.native_literal code = ok r

axiom front.constant_name_spec (uninterpreted : Bool) (n : num.Integer) :
  ∃ r, front.constant_name uninterpreted n = ok r

end pathos_compiled_checker
