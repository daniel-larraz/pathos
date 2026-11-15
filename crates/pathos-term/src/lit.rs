//! Literal values and the `eo::` operators on them (`literal.cpp` in Ethos).

use std::fmt;

use crate::bitvec::BitVec;
use crate::eostring::{EoString, NUM_CODES};
use crate::kind::{EvalOp, LitKind};
use crate::num::{Integer, Rational};
#[cfg(verus_keep_ghost)]
use crate::num::{bits_and, bits_or, bits_xor};
#[cfg(verus_keep_ghost)]
use vstd::{arithmetic::power2::pow2, prelude::*};

/// A literal value.
///
/// Decimal and rational literals hold the same values but are distinct terms,
/// as are hexadecimal and binary literals.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub enum Lit {
    Bool(bool),
    Numeral(Integer),
    Decimal(Rational),
    Rational(Rational),
    Hex(BitVec),
    Binary(BitVec),
    String(EoString),
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Lit {
    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res == kind_of(self@),))]
    pub fn kind(&self) -> LitKind {
        match self {
            Lit::Bool(_) => LitKind::Boolean,
            Lit::Numeral(_) => LitKind::Numeral,
            Lit::Decimal(_) => LitKind::Decimal,
            Lit::Rational(_) => LitKind::Rational,
            Lit::Hex(_) => LitKind::Hexadecimal,
            Lit::Binary(_) => LitKind::Binary,
            Lit::String(_) => LitKind::String,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res@ == (if kind == LitKind::Decimal { Val::Decimal(r@) } else { Val::Rational(r@) }), res.wf(),))]
    fn rational(kind: LitKind, r: Rational) -> Lit {
        if kind == LitKind::Decimal {
            Lit::Decimal(r)
        } else {
            Lit::Rational(r)
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(res => requires b.wf(), ensures res@ == mk_bv(kind, (b.spec_size(), b.spec_value())), res.wf(),))]
    fn bitvec(kind: LitKind, b: BitVec) -> Lit {
        if kind == LitKind::Hexadecimal {
            Lit::Hex(b)
        } else {
            Lit::Binary(b)
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res == (match self { Lit::Bool(b) => Some(*b), _ => None }),))]
    fn as_bool(&self) -> Option<bool> {
        if let Lit::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res == (match self { Lit::Numeral(i) => Some(i), _ => None }),))]
    fn as_int(&self) -> Option<&Integer> {
        if let Lit::Numeral(i) = self {
            Some(i)
        } else {
            None
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res == (match self { Lit::Decimal(r) | Lit::Rational(r) => Some(r), _ => None }),))]
    fn as_rat(&self) -> Option<&Rational> {
        match self {
            Lit::Decimal(r) | Lit::Rational(r) => Some(r),
            _ => None,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res == (match self { Lit::Hex(b) | Lit::Binary(b) => Some(b), _ => None }),))]
    fn as_bv(&self) -> Option<&BitVec> {
        match self {
            Lit::Hex(b) | Lit::Binary(b) => Some(b),
            _ => None,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res == (match self { Lit::String(s) => Some(s), _ => None }),))]
    fn as_str(&self) -> Option<&EoString> {
        if let Lit::String(s) = self {
            Some(s)
        } else {
            None
        }
    }

    /// Applies `op` to literal arguments. Returns `None` when the operator
    /// does not evaluate on them. The caller has checked the arity, and
    /// handles `eo::is_eq`, `eo::ite` and `eo::requires` itself.
    #[cfg_attr(verus_keep_ghost, verus_spec(res =>
        requires forall|i: int| 0 <= i < args@.len() ==> (#[trigger] args@[i]).wf(),
        ensures
            res matches Some(l) ==> l.wf(),
            eval_spec(op, args@) matches Some(expected) ==> match expected {
                Some(v) => res matches Some(l) && l@ == v,
                None => res is None,
            },
    ))]
    // Verus does not take a constructor as a function: no `.map(Lit::Rational)`
    #[allow(clippy::manual_map)]
    pub fn evaluate(op: EvalOp, args: &[&Lit]) -> Option<Lit> {
        let first = *args.first()?;
        // Most operators need all arguments to be of one kind.
        let mixed = matches!(
            op,
            EvalOp::Extract | EvalOp::ToBin | EvalOp::Pow | EvalOp::Log
        );
        let ka = first.kind();
        if !mixed && !Lit::all_of_kind(args, ka) {
            return None;
        }
        match op {
            EvalOp::Not => match first {
                Lit::Bool(b) => Some(Lit::Bool(!b)),
                Lit::Hex(b) | Lit::Binary(b) => Some(Lit::bitvec(ka, b.not())),
                _ => None,
            },
            EvalOp::And | EvalOp::Or | EvalOp::Xor | EvalOp::Add | EvalOp::Mul | EvalOp::Concat => {
                Lit::evaluate_nary(op, ka, args)
            }
            EvalOp::Neg => match first {
                Lit::Numeral(i) => Some(Lit::Numeral(i.neg())),
                Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::rational(ka, r.neg())),
                Lit::Hex(b) | Lit::Binary(b) => Some(Lit::bitvec(ka, b.neg())),
                _ => None,
            },
            EvalOp::Pow => {
                let exp = args.get(1)?.as_int().filter(|e| e.fits_u32())?.to_u32();
                match first {
                    Lit::Numeral(i) => Some(Lit::Numeral(i.pow(exp))),
                    Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::rational(ka, r.pow(exp))),
                    _ => None,
                }
            }
            EvalOp::Log => {
                let base = first.as_int()?;
                let value = match args.get(1)? {
                    Lit::Numeral(i) => i.clone(),
                    Lit::Decimal(r) | Lit::Rational(r) => r.floor(),
                    _ => return None,
                };
                Some(Lit::Numeral(integer_floor_log(base, &value)))
            }
            EvalOp::IntDiv | EvalOp::IntMod => {
                let is_div = op == EvalOp::IntDiv;
                let second = *args.get(1)?;
                match (first, second) {
                    (Lit::Numeral(n), Lit::Numeral(d)) => {
                        if d.sgn() == 0 {
                            return None;
                        }
                        let (q, r) = n.euclidean_qr(d);
                        Some(Lit::Numeral(if is_div { q } else { r }))
                    }
                    _ => {
                        let (a, b) = (first.as_bv()?, second.as_bv()?);
                        if a.size() != b.size() {
                            return None;
                        }
                        Some(Lit::bitvec(
                            ka,
                            if is_div {
                                a.unsigned_div_total(b)
                            } else {
                                a.unsigned_rem_total(b)
                            },
                        ))
                    }
                }
            }
            EvalOp::RatDiv => {
                let second = *args.get(1)?;
                match (first, second) {
                    (Lit::Numeral(n), Lit::Numeral(d)) => match Rational::from_integers(n, d) {
                        Some(q) => Some(Lit::Rational(q)),
                        None => None,
                    },
                    _ => {
                        let (n, d) = (first.as_rat()?, second.as_rat()?);
                        if d.sgn() == 0 {
                            return None;
                        }
                        Some(Lit::Rational(n.div(d)))
                    }
                }
            }
            EvalOp::IsNeg => match first {
                Lit::Numeral(i) => Some(Lit::Bool(i.sgn() == -1)),
                Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::Bool(r.sgn() == -1)),
                _ => None,
            },
            EvalOp::Length => match first {
                Lit::Binary(b) => Some(Lit::Numeral(Integer::from(b.size()))),
                Lit::String(s) => Some(Lit::Numeral(Integer::from(s.len()))),
                _ => None,
            },
            EvalOp::Extract => {
                let i1 = args.get(1)?.as_int()?;
                let i2 = args.get(2)?.as_int()?;
                Lit::evaluate_extract(first, i1, i2)
            }
            EvalOp::ToInt => match first {
                Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::Numeral(r.floor())),
                Lit::Numeral(_) => Some(first.clone()),
                Lit::Binary(b) => Some(Lit::Numeral(b.value().clone())),
                // a string of length one gives its code point
                Lit::String(s) if s.len() == 1 => {
                    Some(Lit::Numeral(Integer::from(s.code_points()[0])))
                }
                _ => None,
            },
            EvalOp::ToRat => match first {
                Lit::Rational(_) => Some(first.clone()),
                Lit::Decimal(r) => Some(Lit::Rational(r.clone())),
                Lit::Numeral(i) => Some(Lit::Rational(Rational::from_integer(i))),
                _ => None,
            },
            EvalOp::ToBin => {
                let size = first.as_int().filter(|s| s.fits_u32())?.to_u32();
                match args.get(1)? {
                    Lit::Numeral(i) => Some(Lit::Binary(BitVec::new(size, i))),
                    Lit::Hex(b) | Lit::Binary(b) => Some(Lit::Binary(BitVec::new(size, b.value()))),
                    _ => None,
                }
            }
            EvalOp::ToString => match first {
                // a code point gives the string of that one character
                Lit::Numeral(i) if i.fits_u32() && i.to_u32() < NUM_CODES => {
                    Some(Lit::String(EoString::from_code_points(vec![i.to_u32()])))
                }
                Lit::String(_) => Some(first.clone()),
                _ => None,
            },
            EvalOp::Gt => {
                let second = *args.get(1)?;
                match (first, second) {
                    (Lit::Numeral(a), Lit::Numeral(b)) => Some(Lit::Bool(a > b)),
                    _ => {
                        if let (Some(a), Some(b)) = (first.as_rat(), second.as_rat()) {
                            return Some(Lit::Bool(a > b));
                        }
                        let (a, b) = (first.as_bv()?, second.as_bv()?);
                        Some(Lit::Bool(a.value() > b.value()))
                    }
                }
            }
            EvalOp::Find => {
                let (s, t) = (first.as_str()?, args.get(1)?.as_str()?);
                Some(Lit::Numeral(match s.find(t) {
                    Some(i) => Integer::from(i),
                    None => Integer::one().neg(),
                }))
            }
            _ => None,
        }
    }

    /// Whether every argument is of the given kind.
    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res == all_kind(args@, kind),))]
    fn all_of_kind(args: &[&Lit], kind: LitKind) -> bool {
        #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
            iter.seq().unref() == args@,
            forall|i: int| 0 <= i < iter.index() ==> kind_of(#[trigger] args@[i]@) == kind,
        ))]
        for a in args {
            if a.kind() != kind {
                return false;
            }
        }
        true
    }

    /// Whether every argument is a bit-vector of the given width.
    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures
        res == forall|i: int| 0 <= i < args@.len() ==> is_bv_of_size(#[trigger] args@[i]@, size as nat),
    ))]
    fn all_of_size(args: &[&Lit], size: u32) -> bool {
        #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
            iter.seq().unref() == args@,
            forall|i: int| 0 <= i < iter.index() ==> is_bv_of_size(#[trigger] args@[i]@, size as nat),
        ))]
        for a in args {
            match a.as_bv() {
                Some(b) if b.size() == size => {}
                _ => {
                    proof! {
                        assert(*a == args@[iter.index() as int]);
                        assert(!is_bv_of_size(args@[iter.index() as int]@, size as nat));
                    }
                    return false;
                }
            }
        }
        true
    }

    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(res =>
        requires
            args@.len() >= 1,
            ka == kind_of(args@[0]@),
            all_kind(args@, ka),
            forall|i: int| 0 <= i < args@.len() ==> (#[trigger] args@[i]).wf(),
        ensures
            res matches Some(l) ==> l.wf(),
            nary_spec(op, args@) matches Some(expected) ==> match expected {
                Some(v) => res matches Some(l) && l@ == v,
                None => res is None,
            },
    ))]
    fn evaluate_nary(op: EvalOp, ka: LitKind, args: &[&Lit]) -> Option<Lit> {
        let rest = &args[1..];
        match args[0] {
            Lit::Bool(b) => {
                let mut res = *b;
                for a in rest {
                    let a = a.as_bool()?;
                    res = match op {
                        EvalOp::And => res && a,
                        EvalOp::Or => res || a,
                        EvalOp::Xor => res != a,
                        _ => return None,
                    };
                }
                Some(Lit::Bool(res))
            }
            Lit::Numeral(i) => {
                let mut res = i.clone();
                #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
                    iter.seq().unref() == rest@,
                    res@ == fold_int(op, args@, iter.index() + 1),
                ))]
                for a in rest {
                    proof! {
                        let k = iter.index() + 1;
                        assert(rest@ == args@.subrange(1, args@.len() as int));
                        assert(k < args@.len());
                        assert(*a == args@[k]);
                        assert(kind_of(args@[k]@) == ka);
                    }
                    let a = a.as_int()?;
                    res = match op {
                        EvalOp::Add => res.add(a),
                        EvalOp::Mul => res.mul(a),
                        _ => return None,
                    };
                }
                Some(Lit::Numeral(res))
            }
            Lit::Decimal(r) | Lit::Rational(r) => {
                let mut res = r.clone();
                #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
                    iter.seq().unref() == rest@,
                    res@ == fold_real(op, args@, iter.index() + 1),
                ))]
                for a in rest {
                    proof! {
                        let k = iter.index() + 1;
                        assert(rest@ == args@.subrange(1, args@.len() as int));
                        assert(k < args@.len());
                        assert(*a == args@[k]);
                        assert(kind_of(args@[k]@) == ka);
                    }
                    let a = a.as_rat()?;
                    res = match op {
                        EvalOp::Add => res.add(a),
                        EvalOp::Mul => res.mul(a),
                        _ => return None,
                    };
                }
                Some(Lit::rational(ka, res))
            }
            Lit::Hex(b) | Lit::Binary(b) => {
                proof! { assert(rest@ == args@.subrange(1, args@.len() as int)); }
                if op != EvalOp::Concat && !Lit::all_of_size(rest, b.size()) {
                    proof! {
                        let i = choose|i: int| 0 <= i < rest@.len() && !is_bv_of_size(#[trigger] rest@[i]@, b.spec_size());
                        assert(rest@[i] == args@[i + 1]);
                        assert(!is_bv_of_size(args@[i + 1]@, bv_of(args@[0]@).0));
                    }
                    return None;
                }
                proof! {
                    if op != EvalOp::Concat {
                        assert forall|i: int| 0 <= i < args@.len() implies is_bv_of_size(#[trigger] args@[i]@, bv_of(args@[0]@).0) by {
                            if i > 0 {
                                assert(rest@[i - 1] == args@[i]);
                                assert(is_bv_of_size(rest@[i - 1]@, b.spec_size()));
                            }
                        }
                    }
                }
                let mut res = b.clone();
                #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
                    iter.seq().unref() == rest@,
                    res.wf(),
                    op != EvalOp::Concat ==> res.spec_size() == b.spec_size(),
                    op == EvalOp::And || op == EvalOp::Or || op == EvalOp::Xor || op == EvalOp::Concat ==>
                        (res.spec_size(), res.spec_value()) == fold_bv(op, args@, iter.index() + 1),
                ))]
                for a in rest {
                    proof! {
                        let k = iter.index() + 1;
                        assert(rest@ == args@.subrange(1, args@.len() as int));
                        assert(k < args@.len());
                        assert(*a == args@[k]);
                        assert(kind_of(args@[k]@) == ka);
                    }
                    let a = a.as_bv()?;
                    res = match op {
                        EvalOp::And => res.and(a),
                        EvalOp::Or => res.or(a),
                        EvalOp::Xor => res.xor(a),
                        EvalOp::Add => res.add(a),
                        EvalOp::Mul => res.mul(a),
                        EvalOp::Concat => res.concat(a),
                        _ => return None,
                    };
                }
                Some(Lit::bitvec(ka, res))
            }
            Lit::String(s) => {
                if op != EvalOp::Concat {
                    return None;
                }
                let mut res = s.clone();
                for a in rest {
                    res = res.concat(a.as_str()?);
                }
                Some(Lit::String(res))
            }
        }
    }

    /// `(eo::extract s i1 i2)`: bits or characters `i1 ..= i2`.
    #[cfg_attr(verus_keep_ghost, verus_spec(res =>
        requires s.wf(),
        ensures
            res matches Some(l) ==> l.wf(),
            s@ matches Val::Hex(n, v) ==> res matches Some(l) && l@ == mk_bv(LitKind::Hexadecimal, extract_spec(n, v, i1@, i2@)),
            s@ matches Val::Binary(n, v) ==> res matches Some(l) && l@ == mk_bv(LitKind::Binary, extract_spec(n, v, i1@, i2@)),
    ))]
    fn evaluate_extract(s: &Lit, i1: &Integer, i2: &Integer) -> Option<Lit> {
        match s {
            Lit::Hex(b) | Lit::Binary(b) => {
                let ka = s.kind();
                let dsize = Integer::from(b.size());
                if i1.sgn() < 0 || i2.sgn() < 0 || i1.gt(&dsize) || dsize.sgn() == 0 {
                    return Some(Lit::bitvec(ka, BitVec::zero(0)));
                }
                let v1 = i1.to_u32();
                let vs = b.size();
                let v2 = if i2.gt(&dsize) { vs - 1 } else { i2.to_u32() };
                if v1 > v2 {
                    return Some(Lit::bitvec(ka, BitVec::zero(0)));
                }
                // Ethos reads past the width when v2 == size; the bits there
                // are zero, so extracting them from the value is the same.
                Some(Lit::bitvec(ka, b.extract(v2, v1)))
            }
            Lit::String(st) => {
                let dsize = Integer::from(st.len());
                if i1.sgn() < 0 || i2.sgn() < 0 || i1.gt(&dsize) || dsize.sgn() == 0 {
                    return Some(Lit::String(EoString::default()));
                }
                let v1 = i1.to_u32() as usize;
                let vs = st.len();
                let v2 = if !dsize.gt(i2) {
                    vs - 1
                } else {
                    i2.to_u32() as usize
                };
                let esize = if v2 >= v1 { v2 + 1 - v1 } else { 0 };
                Some(Lit::String(
                    st.substr(v1.min(vs), esize.min(vs - v1.min(vs))),
                ))
            }
            _ => None,
        }
    }
}

/// The greatest `m >= 0` with `base^m <= value`, or 0 if `base <= 1` or
/// `value <= 0`.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(res => ensures true,))]
fn integer_floor_log(base: &Integer, value: &Integer) -> Integer {
    let one = Integer::one();
    if *base <= one || value.sgn() <= 0 {
        return Integer::zero();
    }
    let mut result = Integer::zero();
    let mut remaining = value.clone();
    while *base <= remaining {
        result = result.add(&one);
        remaining = remaining.floor_div_quotient(base);
    }
    result
}

impl fmt::Display for Lit {
    /// The text of the literal without any decoration: no `#b` prefix and no
    /// quotes. This is `Literal::toString` in Ethos.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Bool(b) => f.write_str(if *b { "true" } else { "false" }),
            Lit::Numeral(i) => write!(f, "{i}"),
            Lit::Decimal(r) | Lit::Rational(r) => write!(f, "{r}"),
            Lit::Hex(b) => f.write_str(&b.to_string_base(16)),
            Lit::Binary(b) => f.write_str(&b.to_string_base(2)),
            Lit::String(s) => write!(f, "{s}"),
        }
    }
}

impl Lit {
    /// Writes the value, for snapshots.
    pub fn write_to(&self, w: &mut crate::codec::Writer) {
        w.u8(self.kind() as u8);
        match self {
            Lit::Bool(b) => w.bool(*b),
            Lit::Numeral(i) => w.str(&i.to_string()),
            Lit::Decimal(q) | Lit::Rational(q) => w.str(&q.to_string()),
            Lit::Hex(bv) | Lit::Binary(bv) => {
                w.u32(bv.size());
                w.str(&bv.value().to_string());
            }
            Lit::String(s) => {
                w.len(s.len());
                for &c in s.code_points() {
                    w.u32(c);
                }
            }
        }
    }

    /// Reads a value written by [`Lit::write_to`]. `None` if the input is
    /// not one.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    pub fn read_from(r: &mut crate::codec::Reader) -> Option<Lit> {
        let kind = *LitKind::ALL.get(usize::from(r.u8()?))?;
        Some(match kind {
            LitKind::Boolean => Lit::Bool(r.bool()?),
            LitKind::Numeral => Lit::Numeral(Integer::parse(r.str()?, 10)?),
            LitKind::Decimal => Lit::Decimal(Rational::parse(r.str()?)?),
            LitKind::Rational => Lit::Rational(Rational::parse(r.str()?)?),
            LitKind::Hexadecimal | LitKind::Binary => {
                let size = r.u32()?;
                let value = Integer::parse(r.str()?, 10)?;
                // a value that does not fit the width is not one we wrote
                if value.sgn() < 0 || (value.sgn() > 0 && value.length() > u64::from(size)) {
                    return None;
                }
                let bv = BitVec::new(size, &value);
                if kind == LitKind::Binary {
                    Lit::Binary(bv)
                } else {
                    Lit::Hex(bv)
                }
            }
            LitKind::String => {
                let n = r.len(4)?;
                let mut codes = Vec::with_capacity(n);
                for _ in 0..n {
                    let c = r.u32()?;
                    if c >= crate::NUM_CODES {
                        return None;
                    }
                    codes.push(c);
                }
                Lit::String(EoString::from_code_points(codes))
            }
        })
    }
}

#[cfg(verus_keep_ghost)]
pub use spec::*;

/// The specification of [`Lit::evaluate`] for the arithmetic operators on
/// numerals and rationals and the bit operators on binaries, in terms of
/// mathematical integers and reals.
#[cfg(verus_keep_ghost)]
mod spec {
    use super::*;

    verus! {

    /// What a literal stands for. A bit-vector is its width and its value.
    pub enum Val {
        Bool(bool),
        Numeral(int),
        Decimal(real),
        Rational(real),
        Hex(nat, int),
        Binary(nat, int),
        String(EoString),
    }

    impl Lit {
        pub open spec fn view(&self) -> Val {
            match self {
                Lit::Bool(b) => Val::Bool(*b),
                Lit::Numeral(i) => Val::Numeral(i@),
                Lit::Decimal(r) => Val::Decimal(r@),
                Lit::Rational(r) => Val::Rational(r@),
                Lit::Hex(b) => Val::Hex(b.spec_size(), b.spec_value()),
                Lit::Binary(b) => Val::Binary(b.spec_size(), b.spec_value()),
                Lit::String(s) => Val::String(*s),
            }
        }

        /// The bit-vector in it, if any, fits its width.
        pub open spec fn wf(&self) -> bool {
            match self {
                Lit::Hex(b) | Lit::Binary(b) => b.wf(),
                _ => true,
            }
        }
    }

    pub open spec fn kind_of(v: Val) -> LitKind {
        match v {
            Val::Bool(_) => LitKind::Boolean,
            Val::Numeral(_) => LitKind::Numeral,
            Val::Decimal(_) => LitKind::Decimal,
            Val::Rational(_) => LitKind::Rational,
            Val::Hex(_, _) => LitKind::Hexadecimal,
            Val::Binary(_, _) => LitKind::Binary,
            Val::String(_) => LitKind::String,
        }
    }

    /// The bit-vector literal of a kind: hexadecimal, or else binary.
    pub open spec fn mk_bv(kind: LitKind, b: (nat, int)) -> Val {
        if kind == LitKind::Hexadecimal { Val::Hex(b.0, b.1) } else { Val::Binary(b.0, b.1) }
    }

    /// The rational literal of a kind: decimal, or else rational.
    pub open spec fn mk_rat(kind: LitKind, r: real) -> Val {
        if kind == LitKind::Decimal { Val::Decimal(r) } else { Val::Rational(r) }
    }

    pub open spec fn int_of(v: Val) -> int {
        match v { Val::Numeral(i) => i, _ => 0 }
    }

    pub open spec fn real_of(v: Val) -> real {
        match v { Val::Decimal(r) | Val::Rational(r) => r, _ => 0real }
    }

    pub open spec fn bv_of(v: Val) -> (nat, int) {
        match v { Val::Hex(n, x) | Val::Binary(n, x) => (n, x), _ => (0, 0) }
    }

    pub open spec fn all_kind(args: Seq<&Lit>, k: LitKind) -> bool {
        forall|i: int| 0 <= i < args.len() ==> kind_of(#[trigger] args[i]@) == k
    }

    pub open spec fn is_bv_of_size(v: Val, size: nat) -> bool {
        match v {
            Val::Hex(n, _) | Val::Binary(n, _) => n == size,
            _ => false,
        }
    }

    pub open spec fn same_sizes(args: Seq<&Lit>) -> bool {
        forall|i: int| 0 <= i < args.len() ==> is_bv_of_size(#[trigger] args[i]@, bv_of(args[0]@).0)
    }

    /// The operators that take any number of arguments of one kind, on
    /// arguments that are all of the kind of the first: see [`eval_spec`].
    pub open spec fn nary_spec(op: EvalOp, args: Seq<&Lit>) -> Option<Option<Val>> {
        let first = args[0]@;
        let k = kind_of(first);
        let n = args.len() as int;
        match first {
            Val::Numeral(_) => if op == EvalOp::Add || op == EvalOp::Mul {
                Some(Some(Val::Numeral(fold_int(op, args, n))))
            } else {
                None
            },
            Val::Decimal(_) | Val::Rational(_) => if op == EvalOp::Add || op == EvalOp::Mul {
                Some(Some(mk_rat(k, fold_real(op, args, n))))
            } else {
                None
            },
            Val::Hex(_, _) | Val::Binary(_, _) => if op == EvalOp::Concat {
                Some(Some(mk_bv(k, fold_bv(op, args, n))))
            } else if op == EvalOp::And || op == EvalOp::Or || op == EvalOp::Xor {
                Some(if same_sizes(args) { Some(mk_bv(k, fold_bv(op, args, n))) } else { None })
            } else {
                None
            },
            _ => None,
        }
    }

    /// `eo::add` and `eo::mul` on two integers.
    pub open spec fn int_op(op: EvalOp, a: int, b: int) -> int {
        if op == EvalOp::Add { a + b } else { a * b }
    }

    /// `eo::add` and `eo::mul` on two rationals.
    pub open spec fn real_op(op: EvalOp, a: real, b: real) -> real {
        if op == EvalOp::Add { a + b } else { a * b }
    }

    /// `eo::and`, `eo::or`, `eo::xor` and `eo::concat` on two bit-vectors. The
    /// width of a concatenation is taken modulo 2^32, and the value cut to it.
    pub open spec fn bv_op(op: EvalOp, a: (nat, int), b: (nat, int)) -> (nat, int) {
        match op {
            EvalOp::And => (a.0, bits_and(a.1 as nat, b.1 as nat) as int),
            EvalOp::Or => (a.0, bits_or(a.1 as nat, b.1 as nat) as int),
            EvalOp::Xor => (a.0, bits_xor(a.1 as nat, b.1 as nat) as int),
            _ => {
                let size = ((a.0 + b.0) % 0x1_0000_0000) as nat;
                (size, (a.1 * pow2(b.0) + b.1) % (pow2(size) as int))
            },
        }
    }

    /// The operator applied from the left to the first `n` arguments.
    pub open spec fn fold_int(op: EvalOp, args: Seq<&Lit>, n: int) -> int
        decreases n,
    {
        if n <= 1 { int_of(args[0]@) } else { int_op(op, fold_int(op, args, n - 1), int_of(args[n - 1]@)) }
    }

    pub open spec fn fold_real(op: EvalOp, args: Seq<&Lit>, n: int) -> real
        decreases n,
    {
        if n <= 1 { real_of(args[0]@) } else { real_op(op, fold_real(op, args, n - 1), real_of(args[n - 1]@)) }
    }

    pub open spec fn fold_bv(op: EvalOp, args: Seq<&Lit>, n: int) -> (nat, int)
        decreases n,
    {
        if n <= 1 { bv_of(args[0]@) } else { bv_op(op, fold_bv(op, args, n - 1), bv_of(args[n - 1]@)) }
    }

    /// `(eo::extract b i1 i2)` on a bit-vector of `size` bits with value `v`:
    /// bits `i1 ..= i2`, with Ethos's rules for indices out of range. The
    /// number of bits is taken modulo 2^32.
    pub open spec fn extract_spec(size: nat, v: int, i1: int, i2: int) -> (nat, int) {
        if i1 < 0 || i2 < 0 || i1 > size || size == 0 {
            (0, 0)
        } else {
            let high = if i2 > size { size - 1 } else { i2 };
            if i1 > high {
                (0, 0)
            } else {
                let count = ((high - i1 + 1) % 0x1_0000_0000) as nat;
                (count, (v / (pow2(i1 as nat) as int)) % (pow2(count) as int))
            }
        }
    }

    /// What [`Lit::evaluate`] gives for the operators and arguments this
    /// specification covers: `Some(Some(v))` if the application evaluates to
    /// `v`, `Some(None)` if it does not evaluate, and `None` where nothing is
    /// specified (the other operators, and these on other kinds of literals).
    pub open spec fn eval_spec(op: EvalOp, args: Seq<&Lit>) -> Option<Option<Val>> {
        if args.len() == 0 {
            Some(None)
        } else {
            let first = args[0]@;
            let k = kind_of(first);
            let n = args.len() as int;
            match op {
                EvalOp::Add | EvalOp::Mul | EvalOp::And | EvalOp::Or | EvalOp::Xor | EvalOp::Concat => {
                    if nary_spec(op, args) is Some && !all_kind(args, k) { Some(None) } else { nary_spec(op, args) }
                },
                EvalOp::Neg => match first {
                    Val::Numeral(i) => Some(if all_kind(args, k) { Some(Val::Numeral(-i)) } else { None }),
                    Val::Decimal(r) | Val::Rational(r) => Some(
                        if all_kind(args, k) { Some(mk_rat(k, -r)) } else { None },
                    ),
                    _ => None,
                },
                // Euclidean division: the remainder is never negative
                EvalOp::IntDiv | EvalOp::IntMod => match first {
                    Val::Numeral(x) => Some(
                        if all_kind(args, k) && n >= 2 && int_of(args[1]@) != 0 {
                            let y = int_of(args[1]@);
                            Some(Val::Numeral(if op == EvalOp::IntDiv { x / y } else { x % y }))
                        } else {
                            None
                        },
                    ),
                    _ => None,
                },
                // the result is a rational, also for decimals
                EvalOp::RatDiv => match first {
                    Val::Numeral(x) => Some(
                        if all_kind(args, k) && n >= 2 && int_of(args[1]@) != 0 {
                            Some(Val::Rational(x as real / int_of(args[1]@) as real))
                        } else {
                            None
                        },
                    ),
                    Val::Decimal(x) | Val::Rational(x) => Some(
                        if all_kind(args, k) && n >= 2 && real_of(args[1]@) != 0real {
                            Some(Val::Rational(x / real_of(args[1]@)))
                        } else {
                            None
                        },
                    ),
                    _ => None,
                },
                EvalOp::Not => match first {
                    Val::Hex(size, v) | Val::Binary(size, v) => Some(
                        if all_kind(args, k) { Some(mk_bv(k, (size, pow2(size) - 1 - v))) } else { None },
                    ),
                    _ => None,
                },
                EvalOp::Extract => match first {
                    Val::Hex(size, v) | Val::Binary(size, v) => Some(
                        if n >= 3 && kind_of(args[1]@) == LitKind::Numeral && kind_of(args[2]@) == LitKind::Numeral {
                            Some(mk_bv(k, extract_spec(size, v, int_of(args[1]@), int_of(args[2]@))))
                        } else {
                            None
                        },
                    ),
                    _ => None,
                },
                _ => None,
            }
        }
    }

    pub assume_specification[ <Lit as Clone>::clone ](x: &Lit) -> (r: Lit)
        ensures r == x;

    /// Assumed: the derived `==` of literals is equality of their values.
    impl vstd::std_specs::cmp::PartialEqSpecImpl for Lit {
        open spec fn obeys_eq_spec() -> bool {
            true
        }

        open spec fn eq_spec(&self, other: &Lit) -> bool {
            *self == *other
        }
    }

    /// `Option::filter`, which Verus's library does not describe.
    #[verifier::allow(undeclared_external_trait)]
    pub assume_specification<T, P: FnOnce(&T) -> bool + core::marker::Destruct>[ Option::<T>::filter ](
        o: Option<T>,
        f: P,
    ) -> (r: Option<T>)
        requires o matches Some(v) ==> f.requires((&v,)),
        ensures r matches Some(v) ==> o == Some(v) && f.ensures((&v,), true);

    } // verus!
}

#[cfg(test)]
mod tests {
    use super::*;

    fn num(s: &str) -> Lit {
        Lit::Numeral(Integer::parse(s, 10).unwrap())
    }

    fn string(s: &str) -> Lit {
        Lit::String(EoString::parse(s, true))
    }

    fn bin(s: &str) -> Lit {
        Lit::Binary(BitVec::parse(s, 2).unwrap())
    }

    #[test]
    fn arithmetic() {
        assert_eq!(
            Lit::evaluate(EvalOp::Add, &[&num("1"), &num("2")]),
            Some(num("3"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::IntDiv, &[&num("-7"), &num("2")]),
            Some(num("-4"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::IntMod, &[&num("-7"), &num("2")]),
            Some(num("1"))
        );
        assert_eq!(Lit::evaluate(EvalOp::IntDiv, &[&num("7"), &num("0")]), None);
        assert_eq!(
            Lit::evaluate(EvalOp::IsNeg, &[&num("-1")]),
            Some(Lit::Bool(true))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Add, &[&num("1"), &Lit::Bool(true)]),
            None
        );
        assert_eq!(
            Lit::evaluate(EvalOp::RatDiv, &[&num("6"), &num("4")])
                .unwrap()
                .to_string(),
            "3/2"
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Log, &[&num("2"), &num("9")]),
            Some(num("3"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Pow, &[&num("2"), &num("10")]),
            Some(num("1024"))
        );
    }

    #[test]
    fn strings() {
        assert_eq!(
            Lit::evaluate(EvalOp::Concat, &[&string("ab"), &string("c")]),
            Some(string("abc"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&string("hello"), &num("1"), &num("3")]),
            Some(string("ell"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&string("hello"), &num("3"), &num("99")]),
            Some(string("lo"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&string("hello"), &num("5"), &num("9")]),
            Some(string(""))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Find, &[&string("abc"), &string("z")]),
            Some(num("-1"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToInt, &[&string("A")]),
            Some(num("65"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToString, &[&num("65")]),
            Some(string("A"))
        );
    }

    #[test]
    fn bitvectors() {
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&bin("10110"), &num("1"), &num("3")]),
            Some(bin("011"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToBin, &[&num("4"), &num("-1")]),
            Some(bin("1111"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Length, &[&bin("0000")]),
            Some(num("4"))
        );
        assert_eq!(Lit::evaluate(EvalOp::Add, &[&bin("01"), &bin("001")]), None);
    }
}
