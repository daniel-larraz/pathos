//! Literal values and the `eo::` operators on them (`literal.cpp` in Ethos).

use std::fmt;

use crate::bitvec::BitVec;
use crate::eostring::{EoString, NUM_CODES};
use crate::kind::{EvalOp, LitKind};
use crate::num::{Integer, Rational};
#[cfg(verus_keep_ghost)]
use crate::num::{bits_and, bits_or, bits_xor, floor_div, int_pow, is_floor, real_pow};
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
    ///
    /// Proved: for the number of arguments the operator takes, the result is
    /// exactly what [`lit_spec`] says, a value or none. (For `eo::extract`
    /// on a string, when the string has fewer than 2^32 code points.)
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(100), verus_spec(res =>
        requires forall|i: int| 0 <= i < args@.len() ==> (#[trigger] args@[i]).wf(),
        ensures
            res matches Some(l) ==> l.wf(),
            args@.len() == lit_arity(op) && short_strings(args@) ==> (match res {
                Some(l) => Some(l@),
                None => None,
            }) == lit_spec(op, vals(args@)),
    ))]
    // Verus does not take a constructor as a function: no `.map(Lit::Rational)`
    #[allow(clippy::manual_map)]
    pub fn evaluate(op: EvalOp, args: &[&Lit]) -> Option<Lit> {
        proof! { lemma_vals(args@); }
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
                let exp = args.get(1)?.as_int()?;
                if !exp.fits_u32() {
                    return None;
                }
                let exp = exp.to_u32();
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
                    Lit::Decimal(r) | Lit::Rational(r) => {
                        let floor = r.floor();
                        proof! { lemma_floor(r@, floor@); }
                        floor
                    }
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
                Lit::Decimal(r) | Lit::Rational(r) => {
                    let floor = r.floor();
                    proof! { lemma_floor(r@, floor@); }
                    Some(Lit::Numeral(floor))
                }
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
                let size = first.as_int()?;
                if !size.fits_u32() {
                    return None;
                }
                let size = size.to_u32();
                match args.get(1)? {
                    Lit::Numeral(i) => Some(Lit::Binary(BitVec::new(size, i))),
                    Lit::Hex(b) | Lit::Binary(b) => Some(Lit::Binary(BitVec::new(size, b.value()))),
                    _ => None,
                }
            }
            EvalOp::ToString => match first {
                // a code point gives the string of that one character
                Lit::Numeral(i) if i.fits_u32() && i.to_u32() < NUM_CODES => {
                    // (Verus has no `vec!`)
                    #[allow(clippy::vec_init_then_push)]
                    let code = {
                        let mut code = Vec::with_capacity(1);
                        code.push(i.to_u32());
                        code
                    };
                    proof! { assert(code@ =~= seq![i@ as u32]); }
                    Some(Lit::String(EoString::from_code_points(code)))
                }
                Lit::String(_) => Some(first.clone()),
                _ => None,
            },
            EvalOp::Gt => {
                let second = *args.get(1)?;
                match (first, second) {
                    (Lit::Numeral(a), Lit::Numeral(b)) => Some(Lit::Bool(a.gt(b))),
                    _ => {
                        if let (Some(a), Some(b)) = (first.as_rat(), second.as_rat()) {
                            return Some(Lit::Bool(a.gt(b)));
                        }
                        let (a, b) = (first.as_bv()?, second.as_bv()?);
                        Some(Lit::Bool(a.value().gt(b.value())))
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

    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verifier::rlimit(100), verus_spec(res =>
        requires
            args@.len() >= 1,
            ka == kind_of(args@[0]@),
            all_kind(args@, ka),
            forall|i: int| 0 <= i < args@.len() ==> (#[trigger] args@[i]).wf(),
            op == EvalOp::And || op == EvalOp::Or || op == EvalOp::Xor || op == EvalOp::Add
                || op == EvalOp::Mul || op == EvalOp::Concat,
        ensures
            res matches Some(l) ==> l.wf(),
            args@.len() == 2 ==> (match res {
                Some(l) => Some(l@),
                None => None,
            }) == nary2(op, args@[0]@, args@[1]@),
    ))]
    fn evaluate_nary(op: EvalOp, ka: LitKind, args: &[&Lit]) -> Option<Lit> {
        let rest = &args[1..];
        proof! {
            assert(rest@ == args@.subrange(1, args@.len() as int));
            // the folds, from their first argument
            assert(fold_int(op, args@, 1) == int_of(args@[0]@));
            assert(fold_real(op, args@, 1) == real_of(args@[0]@));
            assert(fold_bv(op, args@, 1) == bv_of(args@[0]@));
            if args@.len() == 2 {
                assert(rest@.len() == 1 && rest@[0] == args@[1]);
                assert(kind_of(args@[1]@) == ka);
            }
        }
        match args[0] {
            Lit::Bool(b) => {
                let mut res = *b;
                #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
                    iter.seq().unref() == rest@,
                    iter.index() == 0 ==> res == *b,
                    iter.index() >= 1 ==> op == EvalOp::And || op == EvalOp::Or || op == EvalOp::Xor,
                    iter.index() == 1 && args@.len() == 2 ==> (args@[1]@ matches Val::Bool(y) && res == bool_op(op, *b, y)),
                ))]
                for a in rest {
                    proof! {
                        let k = iter.index() + 1;
                        assert(k < args@.len());
                        assert(*a == args@[k]);
                        assert(kind_of(args@[k]@) == ka);
                    }
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
                    iter.index() >= 1 ==> op == EvalOp::Add || op == EvalOp::Mul,
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
                    iter.index() >= 1 ==> op == EvalOp::Add || op == EvalOp::Mul,
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
                #[cfg_attr(verus_keep_ghost, verus_spec(iter => invariant
                    iter.seq().unref() == rest@,
                    iter.index() == 0 ==> res@ == s@,
                    iter.index() == 1 && args@.len() == 2 ==> (args@[1]@ matches Val::String(y) && res@ == s@ + y),
                ))]
                for a in rest {
                    proof! {
                        let k = iter.index() + 1;
                        assert(k < args@.len());
                        assert(*a == args@[k]);
                        assert(kind_of(args@[k]@) == ka);
                    }
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
            s@ matches Val::String(st) ==> (st.len() <= u32::MAX ==>
                (res matches Some(l) && l@ == Val::String(substr_spec(st, i1@, i2@)))),
            !(s@ is Hex || s@ is Binary || s@ is String) ==> res is None,
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
                proof! {
                    if st@.len() <= u32::MAX {
                        assert(v1 == i1@ && v1 <= vs);
                        assert(substr_spec(st@, i1@, i2@) =~= st@.subrange(v1 as int, v1 + (if esize < vs - v1 { esize } else { (vs - v1) as usize })));
                    }
                }
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
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(res => ensures res@ == floor_log(base@, value@),))]
fn integer_floor_log(base: &Integer, value: &Integer) -> Integer {
    let one = Integer::one();
    if !base.gt(&one) || value.sgn() <= 0 {
        return Integer::zero();
    }
    let mut result = Integer::zero();
    let mut remaining = value.clone();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            one@ == 1,
            base@ > 1,
            remaining@ >= 0,
            result@ + floor_log(base@, remaining@) == floor_log(base@, value@),
        decreases remaining@,
    ))]
    while !base.gt(&remaining) {
        proof! { lemma_log_step(base@, remaining@); }
        result = result.add(&one);
        remaining = remaining.floor_div_quotient(base);
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_verify(external))]
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

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Lit {
    /// Writes the value, for snapshots.
    #[cfg_attr(verus_keep_ghost, verus_verify(external))]
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
    #[cfg_attr(verus_keep_ghost, verus_spec(res => ensures res matches Some(l) ==> l.wf(),))]
    pub fn read_from(r: &mut crate::codec::Reader) -> Option<Lit> {
        let kind = LitKind::from_index(r.u8()? as usize)?;
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
        /// A string is its code points.
        String(Seq<u32>),
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
                Lit::String(s) => Val::String(s@),
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

    /// `eo::add` and `eo::mul` on two integers.
    pub open spec fn int_op(op: EvalOp, a: int, b: int) -> int {
        if op == EvalOp::Add { a + b } else { a * b }
    }

    /// `eo::add` and `eo::mul` on two rationals.
    pub open spec fn real_op(op: EvalOp, a: real, b: real) -> real {
        if op == EvalOp::Add { a + b } else { a * b }
    }

    /// `eo::and`, `eo::or`, `eo::xor`, `eo::add`, `eo::mul` and `eo::concat` on
    /// two bit-vectors. The width of a concatenation is taken modulo 2^32, and
    /// the value cut to it.
    pub open spec fn bv_op(op: EvalOp, a: (nat, int), b: (nat, int)) -> (nat, int) {
        match op {
            EvalOp::And => (a.0, bits_and(a.1 as nat, b.1 as nat) as int),
            EvalOp::Or => (a.0, bits_or(a.1 as nat, b.1 as nat) as int),
            EvalOp::Xor => (a.0, bits_xor(a.1 as nat, b.1 as nat) as int),
            EvalOp::Add => (a.0, (a.1 + b.1) % (pow2(a.0) as int)),
            EvalOp::Mul => (a.0, (a.1 * b.1) % (pow2(a.0) as int)),
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

    /// The values of the arguments.
    pub open spec fn vals(args: Seq<&Lit>) -> Seq<Val> {
        Seq::new(args.len(), |i: int| args[i]@)
    }

    pub proof fn lemma_vals(args: Seq<&Lit>)
        ensures
            vals(args).len() == args.len(),
            forall|i: int| 0 <= i < args.len() ==> #[trigger] vals(args)[i] == args[i]@,
    {
    }

    /// The number of arguments each operator of [`lit_spec`] takes; the
    /// same number as `check_arity` allows, where it allows one number.
    pub open spec fn lit_arity(op: EvalOp) -> nat {
        match op {
            EvalOp::Not | EvalOp::Neg | EvalOp::IsNeg | EvalOp::Length | EvalOp::ToInt
            | EvalOp::ToRat | EvalOp::ToString => 1,
            EvalOp::Extract => 3,
            _ => 2,
        }
    }

    /// No string among the arguments has 2^32 code points or more.
    pub open spec fn short_strings(args: Seq<&Lit>) -> bool {
        forall|i: int| 0 <= i < args.len() ==> ((#[trigger] args[i]@) matches Val::String(s) ==> s.len() <= u32::MAX)
    }

    /// `eo::and`, `eo::or` and `eo::xor` on two Booleans.
    pub open spec fn bool_op(op: EvalOp, a: bool, b: bool) -> bool {
        match op {
            EvalOp::And => a && b,
            EvalOp::Or => a || b,
            _ => a != b,
        }
    }

    /// The operators that Ethos reads with any number of arguments, on two
    /// of one kind. (`$eo_and`, `$eo_or`, `$eo_xor`, `$eo_add`, `$eo_mul`
    /// and `$eo_concat` of the desugar plugin.)
    pub open spec fn nary2(op: EvalOp, a: Val, b: Val) -> Option<Val> {
        let k = kind_of(a);
        match (a, b) {
            (Val::Bool(x), Val::Bool(y)) => {
                if op == EvalOp::And || op == EvalOp::Or || op == EvalOp::Xor {
                    Some(Val::Bool(bool_op(op, x, y)))
                } else {
                    None
                }
            },
            (Val::Numeral(x), Val::Numeral(y)) => {
                if op == EvalOp::Add || op == EvalOp::Mul { Some(Val::Numeral(int_op(op, x, y))) } else { None }
            },
            (Val::Decimal(x), Val::Decimal(y)) | (Val::Rational(x), Val::Rational(y)) => {
                if op == EvalOp::Add || op == EvalOp::Mul { Some(mk_rat(k, real_op(op, x, y))) } else { None }
            },
            // Bit-vectors: of one width, except for a concatenation. The
            // plugin has one kind of them; here a hexadecimal and a binary
            // do not mix, and the result is of the kind of the arguments.
            (Val::Hex(w1, v1), Val::Hex(w2, v2)) | (Val::Binary(w1, v1), Val::Binary(w2, v2)) => {
                if op == EvalOp::Concat || w1 == w2 { Some(mk_bv(k, bv_op(op, (w1, v1), (w2, v2)))) } else { None }
            },
            (Val::String(x), Val::String(y)) => {
                if op == EvalOp::Concat { Some(Val::String(x + y)) } else { None }
            },
            _ => None,
        }
    }

    /// `str.substr s i n` of SMT-LIB with `n = i2 - i1 + 1`: the code points
    /// `i1 ..= i2` that the string has.
    pub open spec fn substr_spec(s: Seq<u32>, i1: int, i2: int) -> Seq<u32> {
        if 0 <= i1 < s.len() && i1 <= i2 {
            s.subrange(i1, if i2 + 1 < s.len() { i2 + 1 } else { s.len() as int })
        } else {
            Seq::empty()
        }
    }

    /// The greatest `m >= 0` with `base^m <= value`, or 0 if `base <= 1` or
    /// `value <= 0`: how often `value` can be divided by `base` before it is
    /// below it.
    pub open spec fn floor_log(base: int, value: int) -> int
        decreases value,
    {
        decreases_by(lemma_log_decreases);
        if base <= 1 || value < base {
            0
        } else {
            1 + floor_log(base, value / base)
        }
    }

    #[via_fn]
    proof fn lemma_log_decreases(base: int, value: int) {
        if base > 1 && value >= base {
            vstd::arithmetic::div_mod::lemma_div_decreases(value, base);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(value, base);
        }
    }

    /// One division of [`floor_log`].
    pub proof fn lemma_log_step(base: int, value: int)
        requires base > 1, value >= base,
        ensures
            floor_log(base, value) == 1 + floor_log(base, floor_div(value, base)),
            0 <= floor_div(value, base) < value,
    {
        vstd::arithmetic::div_mod::lemma_div_decreases(value, base);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(value, base);
    }

    /// The greatest integer that is not above `x`.
    pub open spec fn real_floor(x: real) -> int {
        choose|i: int| is_floor(x, i)
    }

    /// There is one such integer.
    pub proof fn lemma_floor(x: real, i: int)
        requires is_floor(x, i),
        ensures real_floor(x) == i,
    {
        let j = real_floor(x);
        assert(is_floor(x, j));
    }

    /// What [`Lit::evaluate`] gives: `Some(v)` if the application of `op` to
    /// literals with the values `a` evaluates to `v`, and `None` if it does
    /// not evaluate and stays as it is.
    ///
    /// Transcribed from Ethos's desugar plugin (`eo_desugar_native.eo`); each
    /// arm names the program it comes from. Where the binary does something
    /// else, this follows the binary, and the comment says "binary:". The
    /// plugin has no decimals and one kind of bit-vector; here a decimal is
    /// not a rational and a hexadecimal is not a binary, and operators that
    /// take two values of one kind do not evaluate on a mix.
    ///
    /// `a` has the number of values the operator takes ([`lit_arity`]).
    pub open spec fn lit_spec(op: EvalOp, a: Seq<Val>) -> Option<Val> {
        let k = kind_of(a[0]);
        // These read arguments of several kinds; the others take one kind.
        let mixed = op == EvalOp::Extract || op == EvalOp::ToBin || op == EvalOp::Pow || op == EvalOp::Log;
        if !mixed && !(forall|i: int| 0 <= i < a.len() ==> kind_of(#[trigger] a[i]) == k) {
            None
        } else {
            match op {
                // $eo_not
                EvalOp::Not => match a[0] {
                    Val::Bool(b) => Some(Val::Bool(!b)),
                    Val::Hex(w, v) | Val::Binary(w, v) => Some(mk_bv(k, (w, pow2(w) - 1 - v))),
                    _ => None,
                },
                // $eo_and, $eo_or, $eo_xor, $eo_add, $eo_mul, $eo_concat
                EvalOp::And | EvalOp::Or | EvalOp::Xor | EvalOp::Add | EvalOp::Mul | EvalOp::Concat => {
                    nary2(op, a[0], a[1])
                },
                // $eo_neg
                EvalOp::Neg => match a[0] {
                    Val::Numeral(i) => Some(Val::Numeral(-i)),
                    Val::Decimal(r) | Val::Rational(r) => Some(mk_rat(k, -r)),
                    Val::Hex(w, v) | Val::Binary(w, v) => Some(mk_bv(k, (w, (-v) % (pow2(w) as int)))),
                    _ => None,
                },
                // $eo_pow. binary: the exponent is from 0 to 2^32 - 1; the
                // plugin's power is total.
                EvalOp::Pow => match a[1] {
                    Val::Numeral(e) => if 0 <= e <= u32::MAX {
                        match a[0] {
                            Val::Numeral(b) => Some(Val::Numeral(int_pow(b, e as nat))),
                            Val::Decimal(b) | Val::Rational(b) => Some(mk_rat(k, real_pow(b, e as nat))),
                            _ => None,
                        }
                    } else {
                        None
                    },
                    _ => None,
                },
                // $eo_log: the base is a numeral, the value is floored
                EvalOp::Log => match a[0] {
                    Val::Numeral(b) => match a[1] {
                        Val::Numeral(v) => Some(Val::Numeral(floor_log(b, v))),
                        Val::Decimal(r) | Val::Rational(r) => Some(Val::Numeral(floor_log(b, real_floor(r)))),
                        _ => None,
                    },
                    _ => None,
                },
                // $eo_zdiv, $eo_zmod: Euclidean on numerals, not by zero; on
                // bit-vectors of one width, by zero all ones and the dividend
                EvalOp::IntDiv | EvalOp::IntMod => match (a[0], a[1]) {
                    (Val::Numeral(x), Val::Numeral(y)) => if y != 0 {
                        Some(Val::Numeral(if op == EvalOp::IntDiv { x / y } else { x % y }))
                    } else {
                        None
                    },
                    (Val::Hex(w1, x), Val::Hex(w2, y)) | (Val::Binary(w1, x), Val::Binary(w2, y)) => if w1 == w2 {
                        Some(mk_bv(k, (w1, if op == EvalOp::IntDiv {
                            if y == 0 { pow2(w1) - 1 } else { x / y }
                        } else {
                            if y == 0 { x } else { x % y }
                        })))
                    } else {
                        None
                    },
                    _ => None,
                },
                // $eo_qdiv: a rational, also for decimals; not by zero
                EvalOp::RatDiv => match (a[0], a[1]) {
                    (Val::Numeral(x), Val::Numeral(y)) => if y != 0 {
                        Some(Val::Rational(x as real / y as real))
                    } else {
                        None
                    },
                    (Val::Decimal(x), Val::Decimal(y)) | (Val::Rational(x), Val::Rational(y)) => if y != 0real {
                        Some(Val::Rational(x / y))
                    } else {
                        None
                    },
                    _ => None,
                },
                // $eo_is_neg
                EvalOp::IsNeg => match a[0] {
                    Val::Numeral(i) => Some(Val::Bool(i < 0)),
                    Val::Decimal(r) | Val::Rational(r) => Some(Val::Bool(r < 0real)),
                    _ => None,
                },
                // $eo_len. binary: not of a hexadecimal
                EvalOp::Length => match a[0] {
                    Val::Binary(w, _) => Some(Val::Numeral(w as int)),
                    Val::String(s) => Some(Val::Numeral(s.len() as int)),
                    _ => None,
                },
                // $eo_extract. binary: on a bit-vector the upper index is cut
                // to the width (`extract_spec`); the plugin gives the bits
                // asked for
                EvalOp::Extract => match (a[1], a[2]) {
                    (Val::Numeral(i1), Val::Numeral(i2)) => match a[0] {
                        Val::Hex(w, v) | Val::Binary(w, v) => Some(mk_bv(k, extract_spec(w, v, i1, i2))),
                        Val::String(s) => Some(Val::String(substr_spec(s, i1, i2))),
                        _ => None,
                    },
                    _ => None,
                },
                // $eo_to_z. binary: not of a hexadecimal
                EvalOp::ToInt => match a[0] {
                    Val::Numeral(i) => Some(Val::Numeral(i)),
                    Val::Decimal(r) | Val::Rational(r) => Some(Val::Numeral(real_floor(r))),
                    Val::Binary(_, v) => Some(Val::Numeral(v)),
                    Val::String(s) => if s.len() == 1 { Some(Val::Numeral(s[0] as int)) } else { None },
                    _ => None,
                },
                // $eo_to_q
                EvalOp::ToRat => match a[0] {
                    Val::Numeral(i) => Some(Val::Rational(i as real)),
                    Val::Decimal(r) | Val::Rational(r) => Some(Val::Rational(r)),
                    _ => None,
                },
                // $eo_to_bin: a binary of the width given, up to 2^32 - 1
                EvalOp::ToBin => match a[0] {
                    Val::Numeral(w) => if 0 <= w <= u32::MAX {
                        match a[1] {
                            Val::Numeral(v) | Val::Hex(_, v) | Val::Binary(_, v) => {
                                Some(Val::Binary(w as nat, v % (pow2(w as nat) as int)))
                            },
                            _ => None,
                        }
                    } else {
                        None
                    },
                    _ => None,
                },
                // $eo_to_str: the string of one code point
                EvalOp::ToString => match a[0] {
                    Val::Numeral(i) => if 0 <= i < NUM_CODES { Some(Val::String(seq![i as u32])) } else { None },
                    Val::String(s) => Some(Val::String(s)),
                    _ => None,
                },
                // $eo_gt. binary: bit-vectors of any two widths are compared;
                // the plugin wants one width
                EvalOp::Gt => match (a[0], a[1]) {
                    (Val::Numeral(x), Val::Numeral(y)) => Some(Val::Bool(x > y)),
                    (Val::Decimal(x), Val::Decimal(y)) | (Val::Rational(x), Val::Rational(y)) => Some(Val::Bool(x > y)),
                    (Val::Hex(_, x), Val::Hex(_, y)) | (Val::Binary(_, x), Val::Binary(_, y)) => Some(Val::Bool(x > y)),
                    _ => None,
                },
                // $eo_find: str.indexof from 0
                EvalOp::Find => match (a[0], a[1]) {
                    (Val::String(s), Val::String(t)) => Some(Val::Numeral(crate::eostring::index_of(s, t, 0))),
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
