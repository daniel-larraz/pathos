//! Arbitrary-precision integers and rationals.
//!
//! These wrap `malachite` so the library can be swapped (design decision 9).
//! Every operation mirrors what Ethos does with GMP in `util/integer.cpp` and
//! `util/rational.h`, including rounding directions.

use std::cmp::Ordering;
use std::fmt;

use malachite_base::num::arithmetic::traits::{DivMod, Floor, ModPowerOf2, Pow, Sign};
use malachite_base::num::basic::traits::{One, Zero};
use malachite_base::num::conversion::traits::{FromStringBase, ToStringBase};
use malachite_base::num::logic::traits::SignificantBits;
use malachite_nz::integer::Integer as MInt;
use malachite_q::Rational as MRat;
#[cfg(verus_keep_ghost)]
use vstd::{arithmetic::power2::pow2, prelude::*};

/// An arbitrary-precision integer.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[cfg_attr(
    verus_keep_ghost,
    verus_verify(external_body),
    verifier::external_derive
)]
pub struct Integer(MInt);

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Integer {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == 0,))]
    pub fn zero() -> Integer {
        Integer(MInt::ZERO)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == 1,))]
    pub fn one() -> Integer {
        Integer(MInt::ONE)
    }

    /// Parses an optionally negated string of digits in `base` (2, 10 or 16).
    /// Returns `None` where GMP would reject the string.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ))]
    pub fn parse(s: &str, base: u8) -> Option<Integer> {
        if s.is_empty() || s == "-" {
            return None;
        }
        MInt::from_string_base(base, s).map(Integer)
    }

    /// The sign: -1, 0 or 1.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r == sign_of(self@),))]
    pub fn sgn(&self) -> i32 {
        match self.0.sign() {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == -self@,))]
    pub fn neg(&self) -> Integer {
        Integer(-&self.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == self@ + y@,))]
    pub fn add(&self, y: &Integer) -> Integer {
        Integer(&self.0 + &y.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == self@ * y@,))]
    pub fn mul(&self, y: &Integer) -> Integer {
        Integer(&self.0 * &y.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == self@ - y@,))]
    pub fn sub(&self, y: &Integer) -> Integer {
        Integer(&self.0 - &y.0)
    }

    /// Whether `self > y`.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r == (self@ > y@),))]
    pub fn gt(&self, y: &Integer) -> bool {
        self.0 > y.0
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == int_pow(self@, exp as nat),))]
    pub fn pow(&self, exp: u32) -> Integer {
        Integer((&self.0).pow(u64::from(exp)))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures self@ >= 0 && y@ >= 0 ==> r@ == bits_or(self@ as nat, y@ as nat),))]
    pub fn bitwise_or(&self, y: &Integer) -> Integer {
        Integer(&self.0 | &y.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures self@ >= 0 && y@ >= 0 ==> r@ == bits_and(self@ as nat, y@ as nat),))]
    pub fn bitwise_and(&self, y: &Integer) -> Integer {
        Integer(&self.0 & &y.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures self@ >= 0 && y@ >= 0 ==> r@ == bits_xor(self@ as nat, y@ as nat),))]
    pub fn bitwise_xor(&self, y: &Integer) -> Integer {
        Integer(&self.0 ^ &y.0)
    }

    /// Two's complement negation of all bits, as `mpz_com`.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == -self@ - 1,))]
    pub fn bitwise_not(&self) -> Integer {
        Integer(!&self.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == self@ * pow2(pow as nat),))]
    pub fn multiply_by_pow2(&self, pow: u32) -> Integer {
        Integer(&self.0 << u64::from(pow))
    }

    /// The remainder of the floor division by `2^exp`; never negative.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == self@ % (pow2(exp as nat) as int),))]
    pub fn mod_by_pow2(&self, exp: u32) -> Integer {
        Integer(MInt::from((&self.0).mod_power_of_2(u64::from(exp))))
    }

    /// Bits `low .. low + bit_count` of the value, as a non-negative integer.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == (self@ % (pow2((low + bit_count) as nat) as int)) / (pow2(low as nat) as int),))]
    pub fn extract_bit_range(&self, bit_count: u32, low: u32) -> Integer {
        let high = u64::from(low) + u64::from(bit_count);
        let rem = MInt::from((&self.0).mod_power_of_2(high));
        Integer(rem >> u64::from(low))
    }

    /// The value `2^amount - 1` shifted left by `size`, or-ed into `self`.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        ensures 0 <= self@ < pow2(size as nat) ==> r@ == self@ + (pow2(amount as nat) - 1) * pow2(size as nat),
    ))]
    pub fn one_extend(&self, size: u32, amount: u32) -> Integer {
        let ones = (MInt::ONE << u64::from(amount)) - MInt::ONE;
        Integer(&self.0 | (ones << u64::from(size)))
    }

    /// The quotient rounded towards negative infinity. `y` must be non-zero.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => requires y@ != 0, ensures r@ == floor_div(self@, y@),))]
    pub fn floor_div_quotient(&self, y: &Integer) -> Integer {
        Integer((&self.0).div_mod(&y.0).0)
    }

    /// The remainder of the floor division. `y` must be non-zero.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => requires y@ != 0, ensures r@ == self@ - y@ * floor_div(self@, y@),))]
    pub fn floor_div_remainder(&self, y: &Integer) -> Integer {
        Integer((&self.0).div_mod(&y.0).1)
    }

    /// Euclidean division: the remainder is never negative. `y` must be
    /// non-zero.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires y@ != 0, ensures r.0@ == self@ / y@, r.1@ == self@ % y@,))]
    pub fn euclidean_qr(&self, y: &Integer) -> (Integer, Integer) {
        let q = self.floor_div_quotient(y);
        let r = self.floor_div_remainder(y);
        // The floor remainder is negative only when `y` is negative.
        if r.sgn() < 0 {
            proof! { lemma_euclid_from_floor(self@, y@); }
            (q.add(&Integer::one()), r.sub(y))
        } else {
            proof! { lemma_euclid_from_floor(self@, y@); }
            (q, r)
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r == (0 <= self@ <= u32::MAX),))]
    pub fn fits_u32(&self) -> bool {
        u32::try_from(&self.0).is_ok()
    }

    /// The value as a `u32`. Meaningful only when [`Integer::fits_u32`].
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures 0 <= self@ <= u32::MAX ==> r == self@,))]
    pub fn to_u32(&self) -> u32 {
        u32::try_from(&self.0).unwrap_or(0)
    }

    /// The number of bits of the absolute value; 1 for zero.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ))]
    pub fn length(&self) -> u64 {
        if self.sgn() == 0 {
            1
        } else {
            self.0.significant_bits()
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ))]
    pub fn to_string_base(&self, base: u8) -> String {
        self.0.to_string_base(base)
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl From<u32> for Integer {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == v,))]
    fn from(v: u32) -> Integer {
        Integer(MInt::from(v))
    }
}

impl From<u64> for Integer {
    fn from(v: u64) -> Integer {
        Integer(MInt::from(v))
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl From<usize> for Integer {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == v,))]
    fn from(v: usize) -> Integer {
        Integer(MInt::from(v))
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An arbitrary-precision rational, always in lowest terms.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[cfg_attr(
    verus_keep_ghost,
    verus_verify(external_body),
    verifier::external_derive
)]
pub struct Rational(MRat);

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Rational {
    /// `n / d`, or `None` when `d` is zero.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures match r { Some(q) => d@ != 0 && q@ == n@ as real / d@ as real, None => d@ == 0 },))]
    pub fn from_integers(n: &Integer, d: &Integer) -> Option<Rational> {
        if d.sgn() == 0 {
            return None;
        }
        Some(Rational(MRat::from_integers_ref(&n.0, &d.0)))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == n@ as real,))]
    pub fn from_integer(n: &Integer) -> Rational {
        Rational(MRat::from(&n.0))
    }

    /// Parses `<integer>` or `<integer>/<integer>`.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ))]
    pub fn parse(s: &str) -> Option<Rational> {
        match s.split_once('/') {
            Some((n, d)) => {
                Rational::from_integers(&Integer::parse(n, 10)?, &Integer::parse(d, 10)?)
            }
            None => Some(Rational::from_integer(&Integer::parse(s, 10)?)),
        }
    }

    /// Parses a decimal such as `-12.50`.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ))]
    pub fn from_decimal(dec: &str) -> Option<Rational> {
        match dec.find('.') {
            Some(i) => {
                let mut digits = String::with_capacity(dec.len());
                digits.push_str(&dec[..i]);
                digits.push_str(&dec[i + 1..]);
                let numerator = Integer::parse(&digits, 10)?;
                let places = u32::try_from(dec.len() - (i + 1)).ok()?;
                let denominator = Integer::from(10u32).pow(places);
                Rational::from_integers(&numerator, &denominator)
            }
            None => Rational::parse(dec),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r == (if self@ < 0real { -1i32 } else if self@ == 0real { 0i32 } else { 1i32 }),))]
    pub fn sgn(&self) -> i32 {
        match self.0.sign() {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures is_floor(self@, r@),))]
    pub fn floor(&self) -> Integer {
        Integer((&self.0).floor())
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == -self@,))]
    pub fn neg(&self) -> Rational {
        Rational(-&self.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == self@ + y@,))]
    pub fn add(&self, y: &Rational) -> Rational {
        Rational(&self.0 + &y.0)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == self@ * y@,))]
    pub fn mul(&self, y: &Rational) -> Rational {
        Rational(&self.0 * &y.0)
    }

    /// `self / y`. `y` must be non-zero.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => requires y@ != 0real, ensures r@ == self@ / y@,))]
    pub fn div(&self, y: &Rational) -> Rational {
        Rational(&self.0 / &y.0)
    }

    /// Whether `self > y`.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r == (self@ > y@),))]
    pub fn gt(&self, y: &Rational) -> bool {
        self.0 > y.0
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == real_pow(self@, exp as nat),))]
    pub fn pow(&self, exp: u32) -> Rational {
        Rational((&self.0).pow(u64::from(exp)))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ))]
    pub fn is_integral(&self) -> bool {
        *self.0.denominator_ref() == 1u32
    }
}

impl fmt::Display for Rational {
    /// Prints `n/d`, with the denominator even when it is 1, as Ethos does.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.sign() == Ordering::Less {
            f.write_str("-")?;
        }
        write!(f, "{}/{}", self.0.numerator_ref(), self.0.denominator_ref())
    }
}

#[cfg(verus_keep_ghost)]
pub use spec::*;

/// What Verus is told about the numbers. `malachite` is not verified: every
/// function above marked `external_body` is trusted to do what its `ensures`
/// says and not to panic when its `requires` holds.
#[cfg(verus_keep_ghost)]
mod spec {
    use super::*;
    use vstd::arithmetic::power2::pow2;
    use vstd::prelude::*;

    verus! {

    impl Integer {
        /// The integer this value stands for.
        pub uninterp spec fn view(&self) -> int;
    }

    impl Rational {
        /// The rational number this value stands for.
        pub uninterp spec fn view(&self) -> real;
    }

    pub open spec fn sign_of(x: int) -> i32 {
        if x < 0 { -1i32 } else if x == 0 { 0i32 } else { 1i32 }
    }

    /// The quotient rounded towards negative infinity, for `y != 0`. Verus's
    /// `/` is Euclidean: it rounds down exactly when the divisor is positive.
    /// `b` to the power `e`.
    pub open spec fn int_pow(b: int, e: nat) -> int
        decreases e,
    {
        if e == 0 { 1 } else { b * int_pow(b, (e - 1) as nat) }
    }

    /// `b` to the power `e`.
    pub open spec fn real_pow(b: real, e: nat) -> real
        decreases e,
    {
        if e == 0 { 1real } else { b * real_pow(b, (e - 1) as nat) }
    }

    /// `i` is the greatest integer that is not above `x`.
    pub open spec fn is_floor(x: real, i: int) -> bool {
        i as real <= x && x < (i + 1) as real
    }

    pub open spec fn floor_div(x: int, y: int) -> int {
        if y > 0 { x / y } else { (-x) / (-y) }
    }

    /// A bitwise operation on natural numbers, bit by bit from the lowest.
    /// `f(false, false)` must be false.
    pub open spec fn bits_op(f: spec_fn(bool, bool) -> bool, a: nat, b: nat) -> nat
        decreases a + b,
    {
        if a == 0 && b == 0 {
            0
        } else {
            2 * bits_op(f, a / 2, b / 2) + (if f(a % 2 == 1, b % 2 == 1) { 1nat } else { 0nat })
        }
    }

    pub open spec fn bits_and(a: nat, b: nat) -> nat {
        bits_op(|x: bool, y: bool| x && y, a, b)
    }

    pub open spec fn bits_or(a: nat, b: nat) -> nat {
        bits_op(|x: bool, y: bool| x || y, a, b)
    }

    pub open spec fn bits_xor(a: nat, b: nat) -> nat {
        bits_op(|x: bool, y: bool| x != y, a, b)
    }

    /// Euclidean division from floor division, as `euclidean_qr` computes it.
    pub proof fn lemma_euclid_from_floor(x: int, y: int)
        requires y != 0,
        ensures
            ({
                let q = floor_div(x, y);
                let r = x - y * q;
                if r < 0 { q + 1 == x / y && r - y == x % y } else { q == x / y && r == x % y }
            }),
    {
        let q = floor_div(x, y);
        let r = x - y * q;
        if y > 0 {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, y);
            vstd::arithmetic::div_mod::lemma_mod_bound(x, y);
        } else {
            let ny = -y;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(-x, ny);
            vstd::arithmetic::div_mod::lemma_mod_bound(-x, ny);
            // -x == ny * q + m with 0 <= m < ny, so x == y * q - m
            let m = (-x) % ny;
            assert(-x == ny * q + m);
            assert(ny * q == -(y * q)) by (nonlinear_arith) requires ny == -y;
            assert(r == -m);
            if m == 0 {
                lemma_euclid_unique(x, y, q, 0);
            } else {
                assert(y * (q + 1) == y * q + y) by (nonlinear_arith);
                lemma_euclid_unique(x, y, q + 1, r - y);
            }
        }
    }

    /// The quotient and remainder of Euclidean division are unique.
    pub proof fn lemma_euclid_unique(x: int, y: int, q: int, r: int)
        requires y != 0, x == y * q + r, 0 <= r, r < (if y > 0 { y } else { -y }),
        ensures q == x / y, r == x % y,
    {
        if y > 0 {
            assert(x == q * y + r) by (nonlinear_arith) requires x == y * q + r;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, y, q, r);
        } else {
            let ny = -y;
            assert(x == (-q) * ny + r) by (nonlinear_arith) requires x == y * q + r, ny == -y;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, ny, -q, r);
            lemma_div_by_negative(x, y);
        }
    }

    /// Division by a negative number, in terms of division by a positive
    /// one: the remainder is the same, and the quotient has the other sign.
    pub proof fn lemma_div_by_negative(x: int, y: int)
        requires y < 0,
        ensures x / y == -(x / (-y)), x % y == x % (-y),
    {
        assert(x / y == -(x / (-y)) && x % y == x % (-y)) by (nonlinear_arith) requires y < 0;
    }

    pub assume_specification[ <Integer as Clone>::clone ](x: &Integer) -> (r: Integer)
        ensures r@ == x@;

    pub assume_specification[ <Rational as Clone>::clone ](x: &Rational) -> (r: Rational)
        ensures r@ == x@;

    } // verus!
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(s: &str) -> Integer {
        Integer::parse(s, 10).unwrap()
    }

    #[test]
    fn parse_and_print() {
        assert_eq!(int("-0012").to_string(), "-12");
        assert_eq!(Integer::parse("ff", 16).unwrap().to_string(), "255");
        assert_eq!(Integer::parse("FF", 16).unwrap().to_string_base(16), "ff");
        assert!(Integer::parse("", 10).is_none());
        assert!(Integer::parse("1a", 10).is_none());
    }

    #[test]
    fn division_matches_gmp() {
        // floor division, as mpz_fdiv_q / mpz_fdiv_r
        assert_eq!(int("-7").floor_div_quotient(&int("2")), int("-4"));
        assert_eq!(int("-7").floor_div_remainder(&int("2")), int("1"));
        assert_eq!(int("7").floor_div_quotient(&int("-2")), int("-4"));
        assert_eq!(int("7").floor_div_remainder(&int("-2")), int("-1"));
        // Euclidean division: the remainder is never negative
        for (x, y, q, r) in [
            ("7", "2", "3", "1"),
            ("-7", "2", "-4", "1"),
            ("7", "-2", "-3", "1"),
            ("-7", "-2", "4", "1"),
            ("6", "-3", "-2", "0"),
        ] {
            assert_eq!(int(x).euclidean_qr(&int(y)), (int(q), int(r)), "{x} / {y}");
        }
    }

    #[test]
    fn bits() {
        assert_eq!(int("-1").mod_by_pow2(4), int("15"));
        assert_eq!(int("5").bitwise_not(), int("-6"));
        assert_eq!(int("182").extract_bit_range(3, 2), int("5"));
        assert_eq!(int("1").one_extend(1, 3), int("15"));
        assert_eq!(int("0").length(), 1);
        assert_eq!(int("8").length(), 4);
        assert!(int("4294967295").fits_u32());
        assert!(!int("4294967296").fits_u32());
        assert!(!int("-1").fits_u32());
    }

    #[test]
    fn rationals() {
        assert_eq!(Rational::parse("6/4").unwrap().to_string(), "3/2");
        assert_eq!(Rational::parse("-6/3").unwrap().to_string(), "-2/1");
        assert_eq!(Rational::parse("5").unwrap().to_string(), "5/1");
        assert!(Rational::parse("1/0").is_none());
        assert_eq!(Rational::from_decimal("-1.50").unwrap().to_string(), "-3/2");
        assert_eq!(Rational::from_decimal("-.5").unwrap().to_string(), "-1/2");
        assert_eq!(Rational::parse("-7/2").unwrap().floor(), int("-4"));
        assert_eq!(Rational::parse("7/2").unwrap().floor(), int("3"));
        assert_eq!(Rational::parse("2/3").unwrap().pow(2).to_string(), "4/9");
    }
}
