//! Fixed-width bit-vectors, as `util/bitvector.cpp` in Ethos.

use crate::num::Integer;
#[cfg(verus_keep_ghost)]
use crate::num::{bits_and, bits_or, bits_xor};
#[cfg(verus_keep_ghost)]
use vstd::{arithmetic::power2::pow2, prelude::*};

/// A bit-vector: a width and a non-negative value below `2^width`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub struct BitVec {
    size: u32,
    value: Integer,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl BitVec {
    /// The bit-vector of the given width holding `value` modulo `2^size`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r.wf(), r.spec_size() == size, r.spec_value() == value@ % (pow2(size as nat) as int),))]
    pub fn new(size: u32, value: &Integer) -> BitVec {
        proof! { lemma_mod_pow2_range(value@, size as nat); }
        BitVec {
            size,
            value: value.mod_by_pow2(size),
        }
    }

    /// The zero bit-vector of the given width.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r.wf(), r.spec_size() == size, r.spec_value() == 0,))]
    pub fn zero(size: u32) -> BitVec {
        proof! { lemma_mod_pow2_range(0, size as nat); }
        BitVec {
            size,
            value: Integer::zero(),
        }
    }

    /// Parses a string of binary (base 2) or hexadecimal (base 16) digits;
    /// the width follows from the number of digits.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r matches Some(b) ==> b.wf(),))]
    pub fn parse(num: &str, base: u8) -> Option<BitVec> {
        let value = Integer::parse(num, base)?;
        let digits = u32::try_from(num.len()).ok()?;
        let size = if base == 16 {
            digits.checked_mul(4)?
        } else {
            digits
        };
        Some(BitVec { size, value })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self.spec_size(),))]
    pub fn size(&self) -> u32 {
        self.size
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r@ == self.spec_value(),))]
    pub fn value(&self) -> &Integer {
        &self.value
    }

    /// The digits in `base`. Binary output is padded to the width;
    /// hexadecimal output is not, as in Ethos.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures true,))]
    pub fn to_string_base(&self, base: u8) -> String {
        let s = self.value.to_string_base(base);
        let size = self.size as usize;
        if base == 2 && size > s.len() {
            let mut out = "0".repeat(size - s.len());
            out.push_str(&s);
            out
        } else if self.size == 0 {
            String::new()
        } else {
            s
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), other.wf(),
        ensures
            r.wf(),
            r.spec_size() == (self.spec_size() + other.spec_size()) % 0x1_0000_0000,
            r.spec_value() == (self.spec_value() * pow2(other.spec_size()) + other.spec_value()) % (pow2(r.spec_size()) as int),
            // unless the width wraps around, nothing is cut off
            self.spec_size() + other.spec_size() <= u32::MAX ==>
                r.spec_value() == self.spec_value() * pow2(other.spec_size()) + other.spec_value(),
    ))]
    pub fn concat(&self, other: &BitVec) -> BitVec {
        proof! { lemma_concat_fits(self.value@, self.size as nat, other.value@, other.size as nat); }
        BitVec::new(
            self.size.wrapping_add(other.size),
            &self.value.multiply_by_pow2(other.size).add(&other.value),
        )
    }

    /// Bits `low ..= high`. Requires `low <= high`. The number of bits is
    /// taken modulo 2^32, as in Ethos: bits `0 ..= 2^32 - 1` are no bits.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), low <= high,
        ensures
            r.wf(),
            r.spec_size() == (high - low + 1) % 0x1_0000_0000,
            r.spec_value() == (self.spec_value() / (pow2(low as nat) as int)) % (pow2(r.spec_size()) as int),
    ))]
    pub fn extract(&self, high: u32, low: u32) -> BitVec {
        let count = (high - low).wrapping_add(1);
        proof! { lemma_extract(self.value@, low as nat, count as nat); }
        BitVec::new(count, &self.value.extract_bit_range(count, low))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), b.wf(),
        ensures
            r.wf(),
            r.spec_size() == self.spec_size(),
            self.spec_size() == b.spec_size() ==>
                r.spec_value() == bits_xor(self.spec_value() as nat, b.spec_value() as nat),
    ))]
    pub fn xor(&self, b: &BitVec) -> BitVec {
        proof! { if self.size == b.size { lemma_bits_xor_fits(self.value@ as nat, b.value@ as nat, self.size as nat); } }
        BitVec::new(self.size, &self.value.bitwise_xor(&b.value))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), b.wf(),
        ensures
            r.wf(),
            r.spec_size() == self.spec_size(),
            self.spec_size() == b.spec_size() ==>
                r.spec_value() == bits_or(self.spec_value() as nat, b.spec_value() as nat),
    ))]
    pub fn or(&self, b: &BitVec) -> BitVec {
        proof! { if self.size == b.size { lemma_bits_or_fits(self.value@ as nat, b.value@ as nat, self.size as nat); } }
        BitVec::new(self.size, &self.value.bitwise_or(&b.value))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), b.wf(),
        ensures
            r.wf(),
            r.spec_size() == self.spec_size(),
            self.spec_size() == b.spec_size() ==>
                r.spec_value() == bits_and(self.spec_value() as nat, b.spec_value() as nat),
    ))]
    pub fn and(&self, b: &BitVec) -> BitVec {
        proof! { if self.size == b.size { lemma_bits_and_fits(self.value@ as nat, b.value@ as nat, self.size as nat); } }
        BitVec::new(self.size, &self.value.bitwise_and(&b.value))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(),
        ensures
            r.wf(),
            r.spec_size() == self.spec_size(),
            r.spec_value() == pow2(self.spec_size()) - 1 - self.spec_value(),
    ))]
    pub fn not(&self) -> BitVec {
        proof! { lemma_not_mod(self.value@, self.size as nat); }
        BitVec::new(self.size, &self.value.bitwise_not())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures
        r.wf(),
        r.spec_size() == self.spec_size(),
        r.spec_value() == (self.spec_value() + b.spec_value()) % (pow2(self.spec_size()) as int),
    ))]
    pub fn add(&self, b: &BitVec) -> BitVec {
        BitVec::new(self.size, &self.value.add(&b.value))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), ensures
        r.wf(),
        r.spec_size() == self.spec_size(),
        r.spec_value() == (-self.spec_value()) % (pow2(self.spec_size()) as int),
    ))]
    pub fn neg(&self) -> BitVec {
        proof! { lemma_neg_mod(self.spec_value(), self.spec_size()); }
        self.not().add(&BitVec::new(self.size, &Integer::one()))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures
        r.wf(),
        r.spec_size() == self.spec_size(),
        r.spec_value() == (self.spec_value() * b.spec_value()) % (pow2(self.spec_size()) as int),
    ))]
    pub fn mul(&self, b: &BitVec) -> BitVec {
        BitVec::new(self.size, &self.value.mul(&b.value))
    }

    /// Unsigned division; division by zero gives all ones.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), y.wf(), ensures
        r.wf(),
        r.spec_size() == self.spec_size(),
        r.spec_value() == (if y.spec_value() == 0 {
            pow2(self.spec_size()) - 1
        } else {
            self.spec_value() / y.spec_value()
        }),
    ))]
    pub fn unsigned_div_total(&self, y: &BitVec) -> BitVec {
        proof! { lemma_div_rem_fit(self.spec_value(), y.spec_value(), self.spec_size()); }
        if y.value.sgn() == 0 {
            // Ethos builds this as 1 one-extended by size - 1 bits; for width
            // zero the count wraps around there, and the result is still
            // reduced modulo 2^0.
            if self.size == 0 {
                proof! { vstd::arithmetic::power2::lemma2_to64(); }
                return BitVec::zero(0);
            }
            proof! {
                // 1 with size - 1 ones above it is 2^size - 1
                vstd::arithmetic::power2::lemma2_to64();
                vstd::arithmetic::power2::lemma_pow2_unfold(self.size as nat);
                vstd::arithmetic::power2::lemma_pow2_pos((self.size - 1) as nat);
                assert(1 + (pow2((self.size - 1) as nat) - 1) * pow2(1) == pow2(self.size as nat) - 1) by (nonlinear_arith)
                    requires pow2(1) == 2, pow2(self.size as nat) == 2 * pow2((self.size - 1) as nat);
            }
            return BitVec::new(self.size, &Integer::one().one_extend(1, self.size - 1));
        }
        BitVec::new(self.size, &self.value.floor_div_quotient(&y.value))
    }

    /// Unsigned remainder; the remainder by zero is the dividend.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => requires self.wf(), y.wf(), ensures
        r.wf(),
        r.spec_size() == self.spec_size(),
        r.spec_value() == (if y.spec_value() == 0 { self.spec_value() } else { self.spec_value() % y.spec_value() }),
    ))]
    pub fn unsigned_rem_total(&self, y: &BitVec) -> BitVec {
        proof! { lemma_div_rem_fit(self.spec_value(), y.spec_value(), self.spec_size()); }
        if y.value.sgn() == 0 {
            return BitVec::new(self.size, &self.value);
        }
        BitVec::new(self.size, &self.value.floor_div_remainder(&y.value))
    }
}

#[cfg(verus_keep_ghost)]
verus! {

impl BitVec {
    /// The width.
    pub closed spec fn spec_size(&self) -> nat {
        self.size as nat
    }

    /// The bits, as a number.
    pub closed spec fn spec_value(&self) -> int {
        self.value@
    }

    /// The value fits the width. Every function here that makes a
    /// bit-vector makes one for which this holds.
    pub closed spec fn wf(&self) -> bool {
        0 <= self.value@ < pow2(self.size as nat)
    }
}

/// The two's complement of a value of `n` bits is its negation modulo
/// `2^n`.
pub proof fn lemma_neg_mod(v: int, n: nat)
    requires 0 <= v < pow2(n),
    ensures (pow2(n) - 1 - v + 1int % (pow2(n) as int)) % (pow2(n) as int) == (-v) % (pow2(n) as int),
{
    vstd::arithmetic::power2::lemma_pow2_pos(n);
    let m = pow2(n) as int;
    if n == 0 {
        vstd::arithmetic::power2::lemma2_to64();
    } else {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(0, n);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::div_mod::lemma_small_mod(1, m as nat);
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(-v, m);
    }
}

/// The quotient and the remainder of values of `n` bits are values of `n`
/// bits, and the quotient rounded down is the Euclidean one.
pub proof fn lemma_div_rem_fit(x: int, y: int, n: nat)
    requires 0 <= x < pow2(n), 0 <= y,
    ensures
        y != 0 ==> 0 <= x / y < pow2(n) && 0 <= x % y < pow2(n)
            && (x / y) % (pow2(n) as int) == x / y
            && (x - y * (x / y)) % (pow2(n) as int) == x % y,
        x % (pow2(n) as int) == x,
        (pow2(n) - 1) % (pow2(n) as int) == pow2(n) - 1,
{
    vstd::arithmetic::power2::lemma_pow2_pos(n);
    lemma_mod_pow2_small(x, n);
    lemma_mod_pow2_small(pow2(n) - 1, n);
    if y != 0 {
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, y);
        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x, 1, y);
        vstd::arithmetic::div_mod::lemma_div_basics(x);
        vstd::arithmetic::div_mod::lemma_mod_bound(x, y);
        vstd::arithmetic::div_mod::lemma_mod_decreases(x as nat, y as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, y);
        lemma_mod_pow2_small(x / y, n);
        lemma_mod_pow2_small(x % y, n);
    }
}

/// A remainder by a power of two is a value of that many bits.
pub proof fn lemma_mod_pow2_range(x: int, n: nat)
    ensures 0 <= x % (pow2(n) as int) < pow2(n),
{
    vstd::arithmetic::power2::lemma_pow2_pos(n);
    vstd::arithmetic::div_mod::lemma_mod_bound(x, pow2(n) as int);
}

/// A value of `n` bits is its own remainder by `2^n`.
pub proof fn lemma_mod_pow2_small(x: int, n: nat)
    requires 0 <= x < pow2(n),
    ensures x % (pow2(n) as int) == x,
{
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, pow2(n));
}

/// A bitwise operation on two values of `n` bits gives a value of `n` bits.
pub proof fn lemma_bits_op_fits(f: spec_fn(bool, bool) -> bool, a: nat, b: nat, n: nat)
    requires a < pow2(n), b < pow2(n), !f(false, false),
    ensures crate::num::bits_op(f, a, b) < pow2(n),
    decreases n,
{
    if n == 0 {
        vstd::arithmetic::power2::lemma2_to64();
        assert(a == 0 && b == 0);
    } else if a == 0 && b == 0 {
        vstd::arithmetic::power2::lemma_pow2_pos(n);
    } else {
        vstd::arithmetic::power2::lemma_pow2_unfold(n);
        lemma_bits_op_fits(f, a / 2, b / 2, (n - 1) as nat);
    }
}

pub proof fn lemma_bits_and_fits(a: nat, b: nat, n: nat)
    requires a < pow2(n), b < pow2(n),
    ensures (bits_and(a, b) as int) % (pow2(n) as int) == bits_and(a, b),
{
    lemma_bits_op_fits(|x: bool, y: bool| x && y, a, b, n);
    lemma_mod_pow2_small(bits_and(a, b) as int, n);
}

pub proof fn lemma_bits_or_fits(a: nat, b: nat, n: nat)
    requires a < pow2(n), b < pow2(n),
    ensures (bits_or(a, b) as int) % (pow2(n) as int) == bits_or(a, b),
{
    lemma_bits_op_fits(|x: bool, y: bool| x || y, a, b, n);
    lemma_mod_pow2_small(bits_or(a, b) as int, n);
}

pub proof fn lemma_bits_xor_fits(a: nat, b: nat, n: nat)
    requires a < pow2(n), b < pow2(n),
    ensures (bits_xor(a, b) as int) % (pow2(n) as int) == bits_xor(a, b),
{
    lemma_bits_op_fits(|x: bool, y: bool| x != y, a, b, n);
    lemma_mod_pow2_small(bits_xor(a, b) as int, n);
}

/// Two's complement negation of all bits, cut to `n` bits, flips the `n`
/// bits.
pub proof fn lemma_not_mod(a: int, n: nat)
    requires 0 <= a < pow2(n),
    ensures (-a - 1) % (pow2(n) as int) == pow2(n) - 1 - a,
{
    let p = pow2(n) as int;
    assert(-a - 1 == (-1) * p + (p - 1 - a)) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(-a - 1, p, -1, p - 1 - a);
}

/// The concatenation of `m` bits and `n` bits has `m + n` bits.
pub proof fn lemma_concat_fits(a: int, m: nat, b: int, n: nat)
    requires 0 <= a < pow2(m), 0 <= b < pow2(n),
    ensures
        0 <= a * pow2(n) + b < pow2(m + n),
        (a * pow2(n) + b) % (pow2(m + n) as int) == a * pow2(n) + b,
{
    vstd::arithmetic::power2::lemma_pow2_adds(m, n);
    let (pm, pn) = (pow2(m) as int, pow2(n) as int);
    assert(0 <= a * pn && a * pn + pn <= pm * pn) by (nonlinear_arith)
        requires 0 <= a < pm, 0 < pn;
    lemma_mod_pow2_small(a * pow2(n) + b, m + n);
}

/// Bits `low .. low + count`: cutting above them first, as
/// `Integer::extract_bit_range` does, changes nothing.
pub proof fn lemma_extract(x: int, low: nat, count: nat)
    requires 0 <= x,
    ensures
        ((x % (pow2(low + count) as int)) / (pow2(low) as int)) % (pow2(count) as int)
            == (x / (pow2(low) as int)) % (pow2(count) as int),
{
    let (l, c) = (pow2(low) as int, pow2(count) as int);
    vstd::arithmetic::power2::lemma_pow2_pos(low);
    vstd::arithmetic::power2::lemma_pow2_pos(count);
    vstd::arithmetic::power2::lemma_pow2_adds(low, count);
    vstd::arithmetic::div_mod::lemma_breakdown(x, l, c);
    let hi = (x / l) % c;
    let lo = x % l;
    // x % (l * c) == l * hi + lo, and lo < l
    vstd::arithmetic::div_mod::lemma_mod_bound(x, l);
    vstd::arithmetic::div_mod::lemma_mod_bound(x / l, c);
    assert(l * hi + lo == hi * l + lo) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(l * hi + lo, l, hi, lo);
    vstd::arithmetic::div_mod::lemma_small_mod(hi as nat, c as nat);
}

pub assume_specification[ <BitVec as Clone>::clone ](x: &BitVec) -> (r: BitVec)
    ensures r == x;

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    fn bv(s: &str) -> BitVec {
        BitVec::parse(s, 2).unwrap()
    }

    #[test]
    fn printing() {
        assert_eq!(bv("0011").to_string_base(2), "0011");
        assert_eq!(
            BitVec::parse("0f", 16).unwrap().to_string_base(2),
            "00001111"
        );
        // hexadecimal output is not padded
        assert_eq!(BitVec::parse("0f", 16).unwrap().to_string_base(16), "f");
        assert_eq!(BitVec::zero(0).to_string_base(2), "");
    }

    #[test]
    fn arithmetic() {
        assert_eq!(bv("1111").add(&bv("0001")), bv("0000"));
        assert_eq!(bv("0001").neg(), bv("1111"));
        assert_eq!(bv("0101").not(), bv("1010"));
        assert_eq!(bv("10").concat(&bv("011")), bv("10011"));
        assert_eq!(bv("10110").extract(3, 1), bv("011"));
        // the number of bits wraps around at 2^32
        assert_eq!(bv("10110").extract(u32::MAX, 0), BitVec::zero(0));
        assert_eq!(bv("0111").unsigned_div_total(&bv("0000")), bv("1111"));
        assert_eq!(bv("0111").unsigned_rem_total(&bv("0000")), bv("0111"));
        assert_eq!(bv("0111").unsigned_div_total(&bv("0010")), bv("0011"));
    }
}
