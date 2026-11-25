//! Generated functions, module 0 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn case_0_eo__24abconv_5fint_5fto_5fbv_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$abconv_int_to_bv_elim"
pub fn eo__24abconv_5fint_5fto_5fbv_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(0), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24abconv_5fint_5fto_5fbv_5felim(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(0), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24abconv_5fint_5fto_5fbv_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24abconv_5fint_5fto_5fbv_5felim(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24abconv_5fint_5fto_5fbv_5felim(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24abconv_5fint_5fto_5fbv_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24abconv_5fint_5fto_5fbv_5felim(s, v10, v13, a2, v9, v8, a0, v2)
}
pub(super) fn more_1_eo__24abconv_5fint_5fto_5fbv_5felim(s: &mut Store, a0: Term, v2: Term, v25: Term, v23: Term) -> CheckResult<Option<Term>> {
let v26 = match eo__24abconv_5fint_5fto_5fbv_5felim(s, a0, v2, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_0_eo__24abconv_5fint_5fto_5fbv_5felim(s: &mut Store, v10: Term, v13: Term, a2: Term, v9: Term, v8: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::IntDiv, &[a2, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v9, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v8, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::IntDiv, &[a2, v24]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24abconv_5fint_5fto_5fbv_5felim(s, a0, v2, v25, v23)
}
pub(super) fn case_0_eo__24abconv_5fubv_5fto_5fint_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$abconv_ubv_to_int_elim"
pub fn eo__24abconv_5fubv_5fto_5fint_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24abconv_5fubv_5fto_5fint_5felim(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24abconv_5fubv_5fto_5fint_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24abconv_5fubv_5fto_5fint_5felim(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24abconv_5fubv_5fto_5fint_5felim(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24abconv_5fubv_5fto_5fint_5felim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_extract, &[v5, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24abconv_5fubv_5fto_5fint_5felim(s, v8, v14, a2, v7, a0, v2)
}
pub(super) fn more_0_eo__24abconv_5fubv_5fto_5fint_5felim(s: &mut Store, v8: Term, v14: Term, a2: Term, v7: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v7, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Mul, &[a2, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24abconv_5fubv_5fto_5fint_5felim(s, a0, v2, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24aci_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn case_1_eo__24aci_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
if a1 != v2 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_@@TypedList.cons"
pub fn eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5f_2b(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v2 = match s.literal(Lit::Rational(v1)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::IsEq, &[v0, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5f_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5f_2b(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_+"
pub fn eo__24eo_5fis_5flist_5fnil_5f_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5f_2b(s, a0);
s.leave();
result
}
pub(super) fn case_3_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5f_2b(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_0_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5f_2a(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v2 = match s.literal(Lit::Rational(v1)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::IsEq, &[v0, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5f_2a(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5f_2a(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_*"
pub fn eo__24eo_5fis_5flist_5fnil_5f_2a(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5f_2a(s, a0);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5f_2a(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_5_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5fbvand(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::Not, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::ToInt, &[v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::IsEq, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5fbvand(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5fbvand(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_bvand"
pub fn eo__24eo_5fis_5flist_5fnil_5fbvand(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5fbvand(s, a0);
s.leave();
result
}
pub(super) fn case_6_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5fbvand(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5fbvor(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsEq, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5fbvor(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5fbvor(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_bvor"
pub fn eo__24eo_5fis_5flist_5fnil_5fbvor(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5fbvor(s, a0);
s.leave();
result
}
pub(super) fn case_7_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5fbvor(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_1_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5fbvxor(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsEq, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5fbvxor(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5fbvxor(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_bvxor"
pub fn eo__24eo_5fis_5flist_5fnil_5fbvxor(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5fbvxor(s, a0);
s.leave();
result
}
pub(super) fn case_8_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5fbvxor(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5fbvadd(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsEq, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5fbvadd(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5fbvadd(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_bvadd"
pub fn eo__24eo_5fis_5flist_5fnil_5fbvadd(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5fbvadd(s, a0);
s.leave();
result
}
pub(super) fn case_9_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5fbvadd(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5fbvmul(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsEq, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5fbvmul(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5fbvmul(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_bvmul"
pub fn eo__24eo_5fis_5flist_5fnil_5fbvmul(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5fbvmul(s, a0);
s.leave();
result
}
pub(super) fn case_10_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5fbvmul(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_11_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn cases_0_2_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::Eq, &[a0, v0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil_str.++"
pub fn eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s, a0);
s.leave();
result
}
pub(super) fn case_12_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_13_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_14_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_15_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn cases_0_3_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_16_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_17_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_18_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_19_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn cases_0_4_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_20_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_5_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_20_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_1_0_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_1_1_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil"
pub fn eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fnil_5f_40_40TypedList_2econs(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fnil_5f_40_40TypedList_2econs(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5f_40_40TypedList_2econs(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_@@TypedList.cons"
pub fn eo__24eo_5fnil_5f_40_40TypedList_2econs(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5f_40_40TypedList_2econs(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5f_40_40TypedList_2econs(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24arith_5fmk_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24arith_5fmk_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v2 = match s.literal(Lit::Rational(v1)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24arith_5fmk_5fzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24arith_5fmk_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24arith_5fmk_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_mk_zero"
pub fn eo__24arith_5fmk_5fzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5fmk_5fzero(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fnil_5f_2b(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24arith_5fmk_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fnil_5f_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5f_2b(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_+"
pub fn eo__24eo_5fnil_5f_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5f_2b(s, a0);
s.leave();
result
}
pub(super) fn case_3_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5f_2b(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_0_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24arith_5fmk_5fone(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24arith_5fmk_5fone(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v2 = match s.literal(Lit::Rational(v1)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24arith_5fmk_5fone(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24arith_5fmk_5fone(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24arith_5fmk_5fone(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_mk_one"
pub fn eo__24arith_5fmk_5fone(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5fmk_5fone(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fnil_5f_2a(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24arith_5fmk_5fone(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fnil_5f_2a(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5f_2a(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_*"
pub fn eo__24eo_5fnil_5f_2a(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5f_2a(s, a0);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5f_2a(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_5_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fnil_5fbvand(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToBin, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Not, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fnil_5fbvand(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5fbvand(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_bvand"
pub fn eo__24eo_5fnil_5fbvand(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5fbvand(s, a0);
s.leave();
result
}
pub(super) fn case_6_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5fbvand(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fnil_5fbvor(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToBin, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fnil_5fbvor(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5fbvor(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_bvor"
pub fn eo__24eo_5fnil_5fbvor(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5fbvor(s, a0);
s.leave();
result
}
pub(super) fn case_7_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5fbvor(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_1_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fnil_5fbvxor(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToBin, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fnil_5fbvxor(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5fbvxor(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_bvxor"
pub fn eo__24eo_5fnil_5fbvxor(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5fbvxor(s, a0);
s.leave();
result
}
pub(super) fn case_8_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5fbvxor(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fnil_5fbvadd(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToBin, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fnil_5fbvadd(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5fbvadd(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_bvadd"
pub fn eo__24eo_5fnil_5fbvadd(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5fbvadd(s, a0);
s.leave();
result
}
pub(super) fn case_9_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5fbvadd(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fnil_5fbvmul(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToBin, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fnil_5fbvmul(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5fbvmul(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_bvmul"
pub fn eo__24eo_5fnil_5fbvmul(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5fbvmul(s, a0);
s.leave();
result
}
pub(super) fn case_10_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5fbvmul(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_11_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_2_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24seq_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_1_eo__24seq_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_seq_2eempty, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24seq_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24seq_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24seq_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$seq_empty"
pub fn eo__24seq_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24seq_5fempty(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fnil_5fstr_2e_2b_2b(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24seq_5fempty(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fnil_5fstr_2e_2b_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil_5fstr_2e_2b_2b(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil_str.++"
pub fn eo__24eo_5fnil_5fstr_2e_2b_2b(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil_5fstr_2e_2b_2b(s, a0);
s.leave();
result
}
pub(super) fn case_12_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fnil_5fstr_2e_2b_2b(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_13_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_14_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_15_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_3_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_16_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_17_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_18_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_19_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn cases_0_4_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_1_0_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_1_1_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil"
pub fn eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBoolean, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fNumeral(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fNumeral(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fNumeral(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_Numeral"
pub fn eo__24eo_5flit_5ftype_5fNumeral(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fNumeral(s, a0);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fNumeral, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5flit_5ftype_5fNumeral(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fRational(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fRational(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fRational(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_Rational"
pub fn eo__24eo_5flit_5ftype_5fRational(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fRational(s, a0);
s.leave();
result
}
pub(super) fn case_2_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fRational, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fRational, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5flit_5ftype_5fRational(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fString(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fString(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fString(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_String"
pub fn eo__24eo_5flit_5ftype_5fString(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fString(s, a0);
s.leave();
result
}
pub(super) fn case_3_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fString, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fString, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5flit_5ftype_5fString(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn cases_0_0_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fBinary(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::Length, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fBinary(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fBinary(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_Binary"
pub fn eo__24eo_5flit_5ftype_5fBinary(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fBinary(s, a0);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBinary, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fBinary, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5flit_5ftype_5fBinary(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_5_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fString, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(v2))
}
pub(super) fn case_6_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDatatypeType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$eo_dd_lookup"
pub fn eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(76), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdd_5flookup(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(76), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24eo_5fdd_5flookup(s, v4, v2, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fdd_5flookup(s: &mut Store, condition: Term, v2: Term, a0: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v5 = match eo__24eo_5fdd_5flookup(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$eo_dtc_resolve"
pub fn eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(85), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdtc_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(85), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fDatatypeTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.construct(Constructor::eo__24emb_5fDatatypeType, &[v4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fedtc_2econs, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fedtc_2econs, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$eo_dt_resolve"
pub fn eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(82), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdt_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(82), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fdtc_5fresolve(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fdt_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24eo_5fdd_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5fdt_5fresolve(s, v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fdd_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdd_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_dd_resolve"
pub fn eo__24eo_5fdd_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdd_5fresolve(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
Ok(Some(Next::Done(a0)))
}
pub(super) fn case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([a0, v2, v4])))
}
// EO program "$eo_typeof_dt_cons_rec"
pub fn eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(820), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(820), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fDtcAppType, &[v4, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_7_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.construct(Constructor::eo__24emb_5fDatatypeType, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fdd_5fresolve(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, v4, v5, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_1_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v9, v10, v8])))
}
pub(super) fn case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([v2, v4, a2])))
}
pub(super) fn step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
}
Err(e) => return Err(e),
}
}
}
// EO program "$eo_typeof_dt_sel_return"
pub fn eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(821), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(821), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_8_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtSel, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match eo__24eo_5fdd_5fresolve(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, v5, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fDatatypeType, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fFunType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_9_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUSort, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_10_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUConst, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(v2))
}
pub(super) fn case_11_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_2_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5ffun_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5ffun_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5ffun_5ftype(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_fun_type"
pub fn eo__24eo_5ftypeof_5ffun_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5ffun_5ftype(s, a0, a1);
s.leave();
result
}
pub(super) fn case_13_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_14_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_15_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_16_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fFunType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_17_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_18_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fBitVec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fBitVec(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fBitVec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_BitVec"
pub fn eo__24eo_5ftypeof_5fBitVec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fBitVec(s, a0);
s.leave();
result
}
pub(super) fn case_20_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fSeq(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fSeq(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fSeq(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_Seq"
pub fn eo__24eo_5ftypeof_5fSeq(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fSeq(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40_40Pair(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40_40Pair(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40_40Pair(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@@Pair"
pub fn eo__24eo_5ftypeof_5f_40_40Pair(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40_40Pair(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40_40pair(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40Pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40_40pair(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40_40pair(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@@pair"
pub fn eo__24eo_5ftypeof_5f_40_40pair(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40_40pair(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2enil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40TypedList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40_40TypedList_2enil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2enil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@@TypedList.nil"
pub fn eo__24eo_5ftypeof_5f_40_40TypedList_2enil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40_40TypedList_2enil(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2econs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
if v2 != a0 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__40_40TypedList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40_40TypedList_2econs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2econs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@@TypedList.cons"
pub fn eo__24eo_5ftypeof_5f_40_40TypedList_2econs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40_40TypedList_2econs(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
if a2 != a1 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_ite"
pub fn eo__24eo_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fite(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fnot(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fnot(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_not"
pub fn eo__24eo_5ftypeof_5fnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fnot(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5for(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5for(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5for(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_or"
pub fn eo__24eo_5ftypeof_5for(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5for(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_3d(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_="
pub fn eo__24eo_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_3d(s, a0, a1);
s.leave();
result
}
pub(super) fn case_1_eo__24get_5flambda_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
// EO program "$get_lambda_type"
pub fn eo__24get_5flambda_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(893), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5flambda_5ftype(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(893), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24get_5flambda_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5flambda_5ftype(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24get_5flambda_5ftype(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24get_5flambda_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.destruct(Constructor::eo__24emb_5fVar, v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = fields[1];
let v10 = match eo__24get_5flambda_5ftype(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fFunType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5flambda(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24get_5flambda_5ftype(s, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5flambda(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5flambda(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_lambda"
pub fn eo__24eo_5ftypeof_5flambda(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5flambda(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5ftypeof_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fdistinct(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_distinct"
pub fn eo__24eo_5ftypeof_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fdistinct(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40purify(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
Ok(Some(a0))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40purify(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40purify(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@purify"
pub fn eo__24eo_5ftypeof_5f_40purify(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40purify(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5f_2b(s: &mut Store, v0: Term, v1: Term, a0: Term) -> CheckResult<Term> {
if v0 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_0_eo__24is_5farith_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24is_5farith_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24is_5farith_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5farith_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5farith_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_arith_type"
pub fn eo__24is_5farith_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5farith_5ftype(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match eo__24is_5farith_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match requires_0_eo__24eo_5ftypeof_5f_2b(s, v0, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_2b(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_+"
pub fn eo__24eo_5ftypeof_5f_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_2b(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5f_3c(s: &mut Store, v0: Term, v1: Term) -> CheckResult<Term> {
if v0 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v2 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_3c(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match eo__24is_5farith_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match requires_0_eo__24eo_5ftypeof_5f_3c(s, v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_3c(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_3c(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_<"
pub fn eo__24eo_5ftypeof_5f_3c(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_3c(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fto_5freal(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fto_5freal(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fto_5freal(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_to_real"
pub fn eo__24eo_5ftypeof_5fto_5freal(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fto_5freal(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fto_5fint(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fto_5fint(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fto_5fint(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_to_int"
pub fn eo__24eo_5ftypeof_5fto_5fint(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fto_5fint(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fis_5fint(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fis_5fint(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fis_5fint(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_is_int"
pub fn eo__24eo_5ftypeof_5fis_5fint(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fis_5fint(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fabs(s: &mut Store, v0: Term, v1: Term, a0: Term) -> CheckResult<Term> {
if v0 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fabs(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24is_5farith_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match requires_0_eo__24eo_5ftypeof_5fabs(s, v0, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fabs(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fabs(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_abs"
pub fn eo__24eo_5ftypeof_5fabs(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fabs(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fdiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fdiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fdiv(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_div"
pub fn eo__24eo_5ftypeof_5fdiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fdiv(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fdivisible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fdivisible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fdivisible(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_divisible"
pub fn eo__24eo_5ftypeof_5fdivisible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fdivisible(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fint_2epow2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fint_2epow2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fint_2epow2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_int.pow2"
pub fn eo__24eo_5ftypeof_5fint_2epow2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fint_2epow2(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fint_2eispow2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fint_2eispow2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fint_2eispow2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_int.ispow2"
pub fn eo__24eo_5ftypeof_5fint_2eispow2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fint_2eispow2(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fselect(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Array, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
if a1 != v5 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fselect(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fselect(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_select"
pub fn eo__24eo_5ftypeof_5fselect(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fselect(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstore(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Array, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
if a1 != v5 { return Ok(None); }
if a2 != v2 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_Array, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstore(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstore(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_store"
pub fn eo__24eo_5ftypeof_5fstore(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstore(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Array, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_Array, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
if v12 != v5 { return Ok(None); }
if v9 != v2 { return Ok(None); }
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@array_deq_diff"
pub fn eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40bvsize(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40bvsize(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40bvsize(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@bvsize"
pub fn eo__24eo_5ftypeof_5f_40bvsize(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40bvsize(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5ftypeof_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_concat"
pub fn eo__24eo_5ftypeof_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fconcat(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fextract(s: &mut Store, v17: Term, v18: Term, a3: Term, a1: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.builtin_core(EvalOp::Neg, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Add, &[a1, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Add, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
pub(super) fn requires_1_eo__24eo_5ftypeof_5fextract(s: &mut Store, v10: Term, v11: Term, a3: Term, a1: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match s.builtin_core(EvalOp::Neg, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[a1, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Add, &[v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Gt, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match requires_0_eo__24eo_5ftypeof_5fextract(s, v17, v18, a3, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
pub(super) fn requires_2_eo__24eo_5ftypeof_5fextract(s: &mut Store, v8: Term, v9: Term, v4: Term, a1: Term, a3: Term) -> CheckResult<Term> {
if v8 != v9 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v8) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v10 = match s.builtin_core(EvalOp::Gt, &[v4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match requires_1_eo__24eo_5ftypeof_5fextract(s, v10, v11, a3, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
pub(super) fn more_3_eo__24eo_5ftypeof_5fextract(s: &mut Store, v6: Term, v25: Term) -> CheckResult<Option<Term>> {
let v26 = match s.apply(v6, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Gt, &[a3, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match requires_2_eo__24eo_5ftypeof_5fextract(s, v8, v9, v4, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5ftypeof_5fextract(s, v6, v25)
}
pub(super) fn body_eo__24eo_5ftypeof_5fextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
let stuck4 = match s.is_stuck(a4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck4 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fextract(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_extract"
pub fn eo__24eo_5ftypeof_5fextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fextract(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5frepeat(s: &mut Store, v6: Term, v7: Term, a1: Term, v3: Term) -> CheckResult<Term> {
if v6 != v7 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v6) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Mul, &[a1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5frepeat(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Gt, &[a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_0_eo__24eo_5ftypeof_5frepeat(s, v6, v7, a1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5ftypeof_5frepeat(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5frepeat(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_repeat"
pub fn eo__24eo_5ftypeof_5frepeat(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5frepeat(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fbvnot(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5fbvnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fbvnot(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_bvnot"
pub fn eo__24eo_5ftypeof_5fbvnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fbvnot(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fbvand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5ftypeof_5fbvand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fbvand(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_bvand"
pub fn eo__24eo_5ftypeof_5fbvand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fbvand(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fbvcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5ftypeof_5fbvcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fbvcomp(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_bvcomp"
pub fn eo__24eo_5ftypeof_5fbvcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fbvcomp(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fbvult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5ftypeof_5fbvult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fbvult(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_bvult"
pub fn eo__24eo_5ftypeof_5fbvult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fbvult(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fzero_5fextend(s: &mut Store, v6: Term, v7: Term, v3: Term, a1: Term) -> CheckResult<Term> {
if v6 != v7 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v6) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v3, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fzero_5fextend(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Gt, &[a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_0_eo__24eo_5ftypeof_5fzero_5fextend(s, v6, v7, v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5ftypeof_5fzero_5fextend(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fzero_5fextend(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_zero_extend"
pub fn eo__24eo_5ftypeof_5fzero_5fextend(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fzero_5fextend(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5frotate_5fleft(s: &mut Store, v6: Term, v7: Term, v3: Term) -> CheckResult<Term> {
if v6 != v7 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v6) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5frotate_5fleft(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Gt, &[a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match requires_0_eo__24eo_5ftypeof_5frotate_5fleft(s, v6, v7, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5ftypeof_5frotate_5fleft(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5frotate_5fleft(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_rotate_left"
pub fn eo__24eo_5ftypeof_5frotate_5fleft(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5frotate_5fleft(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fbvite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
if a2 != a1 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fbvite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fbvite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_bvite"
pub fn eo__24eo_5ftypeof_5fbvite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fbvite(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fbvnego(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5ftypeof_5fbvnego(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fbvnego(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_bvnego"
pub fn eo__24eo_5ftypeof_5fbvnego(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fbvnego(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fbvredand(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5ftypeof_5fbvredand(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fbvredand(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_bvredand"
pub fn eo__24eo_5ftypeof_5fbvredand(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fbvredand(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40bit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40bit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40bit(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@bit"
pub fn eo__24eo_5ftypeof_5f_40bit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40bit(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40from_5fbools(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Add, &[v6, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40from_5fbools(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40from_5fbools(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@from_bools"
pub fn eo__24eo_5ftypeof_5f_40from_5fbools(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40from_5fbools(s, a0, a1);
s.leave();
result
}
pub(super) fn case_114_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_disamb_type_seq.empty"
pub fn eo__24eo_5fdisamb_5ftype_5fseq_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fseq_2eempty(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fdisamb_5ftype_5fseq_2eempty(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fseq_2eempty(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fseq_2eempty(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_seq.empty"
pub fn eo__24eo_5ftypeof_5fseq_2eempty(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fseq_2eempty(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2elen(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2elen(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2elen(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.len"
pub fn eo__24eo_5ftypeof_5fstr_2elen(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2elen(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2e_2b_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2e_2b_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2e_2b_2b(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.++"
pub fn eo__24eo_5ftypeof_5fstr_2e_2b_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2e_2b_2b(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2esubstr(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2esubstr(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2esubstr(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.substr"
pub fn eo__24eo_5ftypeof_5fstr_2esubstr(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2esubstr(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2econtains(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2econtains(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2econtains(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.contains"
pub fn eo__24eo_5ftypeof_5fstr_2econtains(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2econtains(s, a0, a1);
s.leave();
result
}
pub(super) fn more_0_eo__24eo_5ftypeof_5fstr_2ereplace(s: &mut Store, v12: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2ereplace(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
if v10 != v2 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5ftypeof_5fstr_2ereplace(s, v12, v2)
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2ereplace(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2ereplace(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.replace"
pub fn eo__24eo_5ftypeof_5fstr_2ereplace(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2ereplace(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eindexof(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eindexof(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eindexof(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.indexof"
pub fn eo__24eo_5ftypeof_5fstr_2eindexof(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eindexof(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.at"
pub fn eo__24eo_5ftypeof_5fstr_2eat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eat(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2erev(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2erev(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2erev(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.rev"
pub fn eo__24eo_5ftypeof_5fstr_2erev(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2erev(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v4 { return Ok(None); }
let v5 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
if v7 != v2 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eupdate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.update"
pub fn eo__24eo_5ftypeof_5fstr_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eupdate(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eto_5flower(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eto_5flower(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eto_5flower(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.to_lower"
pub fn eo__24eo_5ftypeof_5fstr_2eto_5flower(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eto_5flower(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eto_5fcode(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eto_5fcode(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eto_5fcode(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.to_code"
pub fn eo__24eo_5ftypeof_5fstr_2eto_5fcode(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eto_5fcode(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2efrom_5fcode(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2efrom_5fcode(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2efrom_5fcode(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.from_code"
pub fn eo__24eo_5ftypeof_5fstr_2efrom_5fcode(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2efrom_5fcode(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eis_5fdigit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eis_5fdigit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eis_5fdigit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.is_digit"
pub fn eo__24eo_5ftypeof_5fstr_2eis_5fdigit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eis_5fdigit(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2e_3c(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2e_3c(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2e_3c(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.<"
pub fn eo__24eo_5ftypeof_5fstr_2e_3c(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2e_3c(s, a0, a1);
s.leave();
result
}
pub(super) fn more_0_eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s: &mut Store) -> CheckResult<Option<Term>> {
let v11 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v5 { return Ok(None); }
let v6 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
more_0_eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s)
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.replace_re"
pub fn eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eindexof_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eindexof_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eindexof_5fre(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.indexof_re"
pub fn eo__24eo_5ftypeof_5fstr_2eindexof_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eindexof_5fre(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_140_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_141_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_142_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2eto_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2eto_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2eto_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.to_re"
pub fn eo__24eo_5ftypeof_5fstr_2eto_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2eto_5fre(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fre_2e_2a(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fre_2e_2a(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fre_2e_2a(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_re.*"
pub fn eo__24eo_5ftypeof_5fre_2e_2a(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fre_2e_2a(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fre_2e_5e(s: &mut Store, v3: Term, v4: Term) -> CheckResult<Term> {
if v3 != v4 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fre_2e_5e(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::Gt, &[a1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match requires_0_eo__24eo_5ftypeof_5fre_2e_5e(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5ftypeof_5fre_2e_5e(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fre_2e_5e(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_re.^"
pub fn eo__24eo_5ftypeof_5fre_2e_5e(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fre_2e_5e(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fre_2erange(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5ftypeof_5fre_2erange(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fre_2erange(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_re.range"
pub fn eo__24eo_5ftypeof_5fre_2erange(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fre_2erange(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fre_2e_2b_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fre_2e_2b_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fre_2e_2b_2b(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_re.++"
pub fn eo__24eo_5ftypeof_5fre_2e_2b_2b(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fre_2e_2b_2b(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fre_2eloop(s: &mut Store, v7: Term, v8: Term) -> CheckResult<Term> {
if v7 != v8 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v9 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
pub(super) fn requires_1_eo__24eo_5ftypeof_5fre_2eloop(s: &mut Store, v4: Term, v5: Term, a3: Term) -> CheckResult<Term> {
if v4 != v5 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v6 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Gt, &[a3, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match requires_0_eo__24eo_5ftypeof_5fre_2eloop(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fre_2eloop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a4 != v2 { return Ok(None); }
let v3 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::Gt, &[a1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_1_eo__24eo_5ftypeof_5fre_2eloop(s, v4, v5, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5ftypeof_5fre_2eloop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
let stuck4 = match s.is_stuck(a4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck4 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fre_2eloop(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_re.loop"
pub fn eo__24eo_5ftypeof_5fre_2eloop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fre_2eloop(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fstr_2ein_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5ftypeof_5fstr_2ein_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fstr_2ein_5fre(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_str.in_re"
pub fn eo__24eo_5ftypeof_5fstr_2ein_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fstr_2ein_5fre(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fseq_2eunit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fseq_2eunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fseq_2eunit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_seq.unit"
pub fn eo__24eo_5ftypeof_5fseq_2eunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fseq_2eunit(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fseq_2enth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v4 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fseq_2enth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fseq_2enth(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_seq.nth"
pub fn eo__24eo_5ftypeof_5fseq_2enth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fseq_2enth(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@re_unfold_pos_component"
pub fn eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@strings_deq_diff"
pub fn eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@strings_stoi_result"
pub fn eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@strings_num_occur_re"
pub fn eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre(s, a0, a1);
s.leave();
result
}
pub(super) fn more_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s: &mut Store, a3: Term, v12: Term, v2: Term) -> CheckResult<Option<Term>> {
if a3 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
if v10 != v2 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s, a3, v12, v2)
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@strings_replace_all_result"
pub fn eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s: &mut Store, a3: Term) -> CheckResult<Option<Term>> {
let v11 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v5 { return Ok(None); }
let v6 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
more_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s, a3)
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@strings_replace_re_all_result"
pub fn eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v2 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@witness_string_length"
pub fn eo__24eo_5ftypeof_5f_40witness_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fis(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5ftypeof_5fis(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fis(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_is"
pub fn eo__24eo_5ftypeof_5fis(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fis(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
Ok(Some(a1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fupdate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_update"
pub fn eo__24eo_5ftypeof_5fupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fupdate(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_172_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_174_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5ftuple(s: &mut Store, v2: Term, v3: Term, a0: Term, a1: Term) -> CheckResult<Term> {
if v2 != v3 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v4 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5ftuple_2eupdate(s: &mut Store, a3: Term, v2: Term, a2: Term) -> CheckResult<Term> {
if a3 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a2)
}
pub(super) fn case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fdisamb_5ftype_5fset_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_disamb_type_set.empty"
pub fn eo__24eo_5fdisamb_5ftype_5fset_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdisamb_5ftype_5fset_2eempty(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2eempty(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5fdisamb_5ftype_5fset_2eempty(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2eempty(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2eempty(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.empty"
pub fn eo__24eo_5ftypeof_5fset_2eempty(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2eempty(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2esingleton(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2esingleton(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2esingleton(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.singleton"
pub fn eo__24eo_5ftypeof_5fset_2esingleton(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2esingleton(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2eunion(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2eunion(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2eunion(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.union"
pub fn eo__24eo_5ftypeof_5fset_2eunion(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2eunion(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2emember(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
if v2 != a0 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2emember(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2emember(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.member"
pub fn eo__24eo_5ftypeof_5fset_2emember(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2emember(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2esubset(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2esubset(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2esubset(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.subset"
pub fn eo__24eo_5ftypeof_5fset_2esubset(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2esubset(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2echoose(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2echoose(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2echoose(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.choose"
pub fn eo__24eo_5ftypeof_5fset_2echoose(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2echoose(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2eis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2eis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2eis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.is_empty"
pub fn eo__24eo_5ftypeof_5fset_2eis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2eis_5fempty(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fset_2einsert(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
if v2 != a0 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5ftypeof_5fset_2einsert(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fset_2einsert(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_set.insert"
pub fn eo__24eo_5ftypeof_5fset_2einsert(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fset_2einsert(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v2 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@sets_deq_diff"
pub fn eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5f_2f(s: &mut Store, v0: Term, v1: Term) -> CheckResult<Term> {
if v0 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v2 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_2f(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match eo__24is_5farith_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match requires_0_eo__24eo_5ftypeof_5f_2f(s, v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_2f(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_2f(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_/"
pub fn eo__24eo_5ftypeof_5f_2f(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_2f(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40div_5fby_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40div_5fby_5fzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40div_5fby_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@div_by_zero"
pub fn eo__24eo_5ftypeof_5f_40div_5fby_5fzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40div_5fby_5fzero(s, a0);
s.leave();
result
}
pub(super) fn case_194_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40Monomial, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40_40mon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__40_40Monomial, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40_40mon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40_40mon(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@@mon"
pub fn eo__24eo_5ftypeof_5f_40_40mon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40_40mon(s, a0, a1);
s.leave();
result
}
pub(super) fn case_196_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40Polynomial, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_197_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40Polynomial, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40_40poly(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40Monomial, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40Polynomial, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__40_40Polynomial, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40_40poly(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40_40poly(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@@poly"
pub fn eo__24eo_5ftypeof_5f_40_40poly(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40_40poly(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fforall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fforall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fforall(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_forall"
pub fn eo__24eo_5ftypeof_5fforall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fforall(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24get_5fvar_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(v2))
}
pub(super) fn body_eo__24get_5fvar_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5fvar_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$get_var_type"
pub fn eo__24get_5fvar_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24get_5fvar_5ftype(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fint_5fto_5fbv(s: &mut Store, v3: Term, v4: Term, a1: Term) -> CheckResult<Term> {
if v3 != v4 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v5 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fint_5fto_5fbv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::Gt, &[a1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match requires_0_eo__24eo_5ftypeof_5fint_5fto_5fbv(s, v3, v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5ftypeof_5fint_5fto_5fbv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fint_5fto_5fbv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_int_to_bv"
pub fn eo__24eo_5ftypeof_5fint_5fto_5fbv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fint_5fto_5fbv(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40_40aci_5fsorted(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
Ok(Some(a1))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40_40aci_5fsorted(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40_40aci_5fsorted(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@@aci_sorted"
pub fn eo__24eo_5ftypeof_5f_40_40aci_5fsorted(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40_40aci_5fsorted(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40const(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
Ok(Some(a2))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40const(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40const(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_@const"
pub fn eo__24eo_5ftypeof_5f_40const(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_40const(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fapply(s: &mut Store, v5: Term, a1: Term, v2: Term) -> CheckResult<Term> {
if v5 != a1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v5) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(v2)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.is_node(v4, Some(Constructor::eo__24emb_5fFunType)) { Ok(v) => v, Err(e) => return Err(e) };
if !v6 { return Ok(None); }
let v7 = match requires_0_eo__24eo_5ftypeof_5fapply(s, v5, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn requires_1_eo__24eo_5ftypeof_5fapply(s: &mut Store, v1: Term, a1: Term, v2: Term) -> CheckResult<Term> {
if v1 != a1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(v2)
}
pub(super) fn case_1_eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match requires_1_eo__24eo_5ftypeof_5fapply(s, v1, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_apply"
pub fn eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fapply(s, a0, a1);
s.leave();
result
}
// EO program "$eo_typeof"
pub fn eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_type(TypeCacheKind::Eunoia, cache_args[0]) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_type(TypeCacheKind::Eunoia, cache_args[0], value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_2_0_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_1_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_2_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_3_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_12_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.is_node(v4, Some(Constructor::eo__24emb_5fFunType)) { Ok(v) => v, Err(e) => return Err(e) };
if !v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5ffun_5ftype(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_19_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fBitVec(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_21_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fSeq(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_22_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40Pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40Pair(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_23_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40pair(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_24_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fSeq(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_25_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40_40TypedList_2enil(s, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_26_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40TypedList_2econs(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_27_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fite(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_28_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fnot(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_29_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5for(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_30_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5for(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_31_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5for(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_32_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5for(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_33_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_3d(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_34_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_lambda, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5flambda(s, v7, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_35_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fdistinct(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_36_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40purify(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_37_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_38_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_39_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_40_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_3c(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_41_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_3c(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_42_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_3c(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_43_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_3c(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_44_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fto_5freal(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_45_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fto_5fint(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_46_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_is_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fis_5fint(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_47_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fabs(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_48_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fabs(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_49_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdiv(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_50_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdiv(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_51_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_divisible, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdivisible(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_52_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fint_2epow2(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_53_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fint_2epow2(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_54_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fint_2eispow2(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_55_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdiv(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_56_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdiv(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_57_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40int_5fdiv_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fint_2epow2(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_58_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40mod_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fint_2epow2(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_59_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Array, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40Pair(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_60_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fselect(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_61_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstore(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_62_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40array_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_63_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40bvsize(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_64_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fconcat(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_65_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_extract, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fextract(s, v6, v4, v7, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_66_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_repeat, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5frepeat(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_67_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fbvnot(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_68_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_69_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_70_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvnand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_71_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvnor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_72_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_73_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxnor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_74_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvcomp(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_75_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fbvnot(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_76_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_77_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_78_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_79_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_80_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_81_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsdiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_82_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsrem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_83_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsmod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_84_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_85_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_86_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvugt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_87_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvuge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_88_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_89_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_90_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_91_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_92_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_93_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_94_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_95_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_zero_5fextend, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5fzero_5fextend(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_96_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_sign_5fextend, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5fzero_5fextend(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_97_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_rotate_5fleft, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5frotate_5fleft(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_98_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_rotate_5fright, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5frotate_5fleft(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_99_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fbvite(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_100_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvuaddo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_101_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvnego, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fbvnego(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_102_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsaddo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_103_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvumulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_104_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsmulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_105_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvusubo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_106_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvssubo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_107_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsdivo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_108_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvultbv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvcomp(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_109_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsltbv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fbvcomp(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_110_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvredand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fbvredand(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_111_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvredor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fbvredand(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_112_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo__40bit, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5f_40bit(s, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_113_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40from_5fbools(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_115_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5ftypeof_5fseq_2eempty(s, v2, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_116_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2elen(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_117_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2e_2b_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_118_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2esubstr(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_119_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2econtains(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_120_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2ereplace(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_121_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2eindexof(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_122_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2eat(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_123_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2econtains(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_124_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2esuffixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2econtains(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_125_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2erev(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_126_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2eupdate(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_127_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2eto_5flower(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_128_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2eto_5flower(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_129_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2eto_5fcode(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_130_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2efrom_5fcode(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_131_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eis_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2eis_5fdigit(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_132_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2eto_5fcode(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_133_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2efrom_5fcode(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_134_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2e_3c(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_135_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2e_3c(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_136_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2ereplace(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_137_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_138_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2ereplace_5fre(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_139_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2eindexof_5fre(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_143_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2eto_5fre(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_144_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fre_2e_2a(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_145_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fre_2e_2a(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_146_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_re_2e_5e, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5fre_2e_5e(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_147_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2eopt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fre_2e_2a(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_148_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fre_2e_2a(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_149_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fre_2erange(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_150_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fre_2e_2b_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_151_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fre_2e_2b_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_152_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fre_2e_2b_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_153_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fre_2e_2b_2b(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_154_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_re_2eloop, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fre_2eloop(s, v6, v4, v7, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_155_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fstr_2ein_5fre(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_156_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fseq_2eunit(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_157_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fseq_2enth(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_158_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40re_5funfold_5fpos_5fcomponent, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_159_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_160_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_161_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fstr_2eto_5fcode(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_162_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdiv(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_163_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_164_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_165_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2eindexof(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_166_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof_5fstr_2eindexof_5fre(s, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_167_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match eo__24eo_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult(s, v13, v14, v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_168_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match eo__24eo_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult(s, v13, v14, v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_169_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40witness_5fstring_5flength, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5f_40witness_5fstring_5flength(s, v4, v1, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_170_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_is, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5fis(s, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_171_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.destruct(Constructor::eo_update, v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = fields[0];
let v8 = match eo__24eo_5ftypeof(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof_5fupdate(s, v8, v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_173_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40Pair(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_175_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5ftuple(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_176_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_tuple_2eselect, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5ftuple_2eselect(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_177_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.destruct(Constructor::eo_tuple_2eupdate, v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = fields[0];
let v8 = match eo__24eo_5ftypeof(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof_5ftuple_2eupdate(s, v8, v7, v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_178_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fSeq(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_179_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_set_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5ftypeof_5fset_2eempty(s, v2, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_180_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fset_2esingleton(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_181_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fset_2eunion(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_182_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fset_2eunion(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_183_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eminus, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fset_2eunion(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_184_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fset_2emember(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_185_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2esubset, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fset_2esubset(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_186_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2echoose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fset_2echoose(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_187_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2eis_5fempty, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fset_2eis_5fempty(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_188_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2eis_5fsingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fset_2eis_5fempty(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_189_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2einsert, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fset_2einsert(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_190_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40sets_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_191_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_2f(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_192_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_2f(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_193_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40div_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40div_5fby_5fzero(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_195_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40mon(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_198_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40poly(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_199_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fforall(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_200_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fforall(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_201_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40quantifiers_5fskolemize, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize(s, v3, v1, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_202_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_int_5fto_5fbv, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof_5fint_5fto_5fbv(s, v5, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_203_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40bvsize(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_204_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_sbv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40bvsize(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_205_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_40_40aci_5fsorted(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_206_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40const, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5f_40const(s, v3, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_207_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fapply(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_3_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_4_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_5_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_20_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_21_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_22_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_23_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_6_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_24_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_25_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_26_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_27_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_7_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_28_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_29_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_30_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_31_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_8_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_32_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_33_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_34_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_35_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_9_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_36_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_37_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_38_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_39_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_10_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_40_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_41_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_42_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_43_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_11_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_44_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_45_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_46_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_47_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_12_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_48_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_49_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_50_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_51_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_13_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_52_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_53_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_54_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_55_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_14_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_56_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_57_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_58_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_59_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_15_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_60_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_61_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_62_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_63_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_16_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_64_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_65_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_66_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_67_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_17_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_68_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_69_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_70_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_71_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_18_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_72_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_73_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_74_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_75_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_19_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_76_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_77_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_78_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_79_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_20_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_80_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_81_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_82_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_83_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_21_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_84_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_85_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_86_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_87_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_22_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_88_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_89_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_90_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_91_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_23_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_92_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_93_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_94_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_95_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_24_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_96_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_97_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_98_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_99_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_25_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_100_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_101_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_102_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_103_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_26_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_104_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_105_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_106_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_107_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_27_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_108_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_109_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_110_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_111_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_28_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_112_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_113_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_114_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_115_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_29_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_116_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_117_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_118_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_119_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_30_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_120_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_121_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_122_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_123_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_31_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_124_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_125_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_126_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_127_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_32_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_128_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_129_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_130_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_131_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_33_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_132_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_133_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_134_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_135_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_34_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_136_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_137_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_138_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_139_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_35_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_140_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_141_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_142_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_143_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_36_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_144_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_145_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_146_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_147_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_37_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_148_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_149_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_150_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_151_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_38_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_152_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_153_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_154_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_155_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_39_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_156_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_157_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_158_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_159_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_40_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_160_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_161_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_162_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_163_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_41_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_164_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_165_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_166_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_167_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_42_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_168_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_169_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_170_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_171_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_43_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_172_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_173_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_174_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_175_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_44_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_176_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_177_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_178_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_179_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_45_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_180_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_181_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_182_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_183_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_46_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_184_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_185_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_186_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_187_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_47_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_188_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_189_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_190_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_191_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_48_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_192_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_193_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_194_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_195_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_49_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_196_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_197_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_198_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_199_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_50_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_200_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_201_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_202_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_203_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_51_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_204_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_205_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_206_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_207_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_6_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_7_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_2_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_8_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_9_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_10_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_11_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_3_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_12_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_13_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_14_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_15_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_4_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_16_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_17_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_18_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_19_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_5_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_20_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_21_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_22_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_23_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_6_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_24_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_25_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_26_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_27_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_7_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_28_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_29_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_30_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_31_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_8_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_32_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_33_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_34_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_35_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_9_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_36_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_37_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_38_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_39_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_10_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_40_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_41_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_42_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_43_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_11_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_44_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_45_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_46_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_47_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_12_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_48_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_49_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_50_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_51_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_0_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_0_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_1_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_2_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_3_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_1_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_4_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_5_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_6_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_7_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_2_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_8_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_9_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_10_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_11_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_3_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_12_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$eo_typeof_@quantifiers_skolemize"
pub fn eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(796), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(796), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match eo__24get_5fnth_5fvar_5ftype(s, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
// EO program "$eo_typeof_tuple"
pub fn eo__24eo_5ftypeof_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(874), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5ftuple(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(874), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5ftuple(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5ftypeof_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_list(EvalOp::ListLength, &[v0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsOk, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match requires_0_eo__24eo_5ftypeof_5ftuple(s, v2, v3, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
// EO program "$eo_typeof_tuple.select"
pub fn eo__24eo_5ftypeof_5ftuple_2eselect(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(875), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5ftuple_2eselect(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(875), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof_5ftuple_2eselect(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5ftuple_2eselect(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5ftypeof_5ftuple_2eselect(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_list(EvalOp::ListNth, &[v1, a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
// EO program "$eo_typeof_tuple.update"
pub fn eo__24eo_5ftypeof_5ftuple_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(876), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5ftuple_2eupdate(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(876), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof_5ftuple_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5ftuple_2eupdate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5ftypeof_5ftuple_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_list(EvalOp::ListNth, &[v1, a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match requires_0_eo__24eo_5ftypeof_5ftuple_2eupdate(s, a3, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$get_nth_var_type"
pub fn eo__24get_5fnth_5fvar_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(894), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5fnth_5fvar_5ftype(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(894), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24get_5fnth_5fvar_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5fnth_5fvar_5ftype(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24get_5fnth_5fvar_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListNth, &[v6, v5, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5fvar_5ftype(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
// The list operators. They ask generated functions whether a term ends a
// list and for the empty list of a type (`$eo_is_list_nil`, `$eo_nil`,
// `$eo_typeof`), so this is not part of the runtime that the generated
// code rests on: the generator puts it among the generated functions,
// after those three and before the functions that use a list operator.
impl Store {
    /// Ethos-style primitive evaluation over already evaluated values:
    /// any operator. (Generated code calls `builtin_core` or
    /// `builtin_list`, whichever its operator needs.)
    pub fn builtin(&mut self, op: EvalOp, args: &[Term]) -> CheckResult<Term> {
        if op.is_list_op() {
            self.builtin_list(op, args)
        } else {
            self.builtin_core(op, args)
        }
    }
    /// A list operator.
    pub(crate) fn builtin_list(&mut self, op: EvalOp, args: &[Term]) -> CheckResult<Term> {
        if !Self::takes(op, args.len()) {
            return Ok(self.stuck());
        }
        self.check_handles(args)?;
        if self.any_stuck(args) {
            return Ok(self.stuck());
        }
        self.list_builtin(op, args)
    }
    /// Whether the list constructor `f` nests to the left.
    fn is_left_assoc(&self, f: Term) -> CheckResult<bool> {
        Ok(match self.view(f)? {
            TermData::Node(c, _) => c.is_left_assoc(),
            _ => false,
        })
    }
    /// The next element of a list of `f` and the rest of the list, or
    /// `None` where the list of applications of `f` ends. `count` is the
    /// number of elements taken so far.
    fn list_step(
        &self,
        f: Term,
        left: bool,
        list: Term,
        count: usize,
    ) -> CheckResult<Option<(Term, Term)>> {
        let Some((g, b)) = self.unapply(list)? else {
            return Ok(None);
        };
        let Some((head, a)) = self.unapply(g)? else {
            return Ok(None);
        };
        if f != head {
            return Ok(None);
        }
        if count as u64 >= self.limits.calls {
            return Err(CheckError::Limit);
        }
        Ok(Some(if left { (b, a) } else { (a, b) }))
    }
    /// The elements of a list of `f`, and where its applications of `f` end.
    fn list_elements(&self, f: Term, left: bool, list: Term) -> CheckResult<(Vec<Term>, Term)> {
        let mut out = Vec::new();
        let mut list = list;
        let mut more = true;
        while more {
            match self.list_step(f, left, list, out.len())? {
                Some((element, rest)) => {
                    out.push(element);
                    list = rest;
                }
                None => more = false,
            }
        }
        Ok((out, list))
    }
    fn list_parts(&mut self, f: Term, list: Term) -> CheckResult<Option<(Vec<Term>, Term)>> {
        let left = self.is_left_assoc(f)?;
        let (out, list) = self.list_elements(f, left, list)?;
        let is_nil = generated::eo__24eo_5fis_5flist_5fnil(self, f, list)?;
        match self.boolean_value(is_nil, false)? {
            Some(true) => {}
            _ => return Ok(None),
        }
        Ok(Some((out, list)))
    }
    /// The list of `f` with the element `e` before `tail`.
    fn list_cons(&mut self, f: Term, left: bool, e: Term, tail: Term) -> CheckResult<Term> {
        let first = self.apply(f, if left { tail } else { e })?;
        self.apply(first, if left { e } else { tail })
    }
    fn list_build(&mut self, f: Term, elems: &[Term], nil: Term) -> CheckResult<Term> {
        let left = self.is_left_assoc(f)?;
        let mut list = nil;
        let mut i = elems.len();
        while i > 0 {
            i -= 1;
            list = self.list_cons(f, left, elems[i], list)?;
        }
        Ok(list)
    }
    fn list_builtin(&mut self, op: EvalOp, a: &[Term]) -> CheckResult<Term> {
        let f = a[0];
        match op {
            EvalOp::Nil => generated::eo__24eo_5fnil(self, f, a[1]),
            EvalOp::ListRepeat => self.list_repeat(f, a[1], a[2]),
            EvalOp::Cons => self.list_cons_op(f, a[1], a[2]),
            EvalOp::ListConcat => self.list_concat(f, a[1], a[2]),
            EvalOp::ListMinclude | EvalOp::ListMeq => self.list_inclusion(op, f, a[1], a[2]),
            EvalOp::ListDiff | EvalOp::ListInter => self.list_selection(op, f, a[1], a[2]),
            _ => self.list_of_one(op, f, a),
        }
    }
    /// The list of `f` that is empty for elements of the type of `x`.
    fn list_nil_for(&mut self, f: Term, x: Term) -> CheckResult<Term> {
        let ty = generated::eo__24eo_5ftypeof(self, x)?;
        generated::eo__24eo_5fnil(self, f, ty)
    }
    fn list_repeat(&mut self, f: Term, x: Term, count: Term) -> CheckResult<Term> {
        let Some(n) = self.object_index(count)? else {
            return Ok(self.stuck());
        };
        if u64::from(n) > self.limits.calls {
            return Err(CheckError::Limit);
        }
        let nil = self.list_nil_for(f, x)?;
        let elems = vec![x; n as usize];
        self.list_build(f, &elems, nil)
    }
    fn list_cons_op(&mut self, f: Term, x: Term, list: Term) -> CheckResult<Term> {
        let Some((tail, nil)) = self.list_parts(f, list)? else {
            return Ok(self.stuck());
        };
        let mut elems = Vec::with_capacity(tail.len() + 1);
        elems.push(x);
        append_terms(&mut elems, &tail);
        self.list_build(f, &elems, nil)
    }
    /// The elements of two lists of `f` that end in the same nil, with
    /// that nil; `None` if one is not a list or the ends differ.
    #[allow(clippy::type_complexity)]
    fn list_pair(
        &mut self,
        f: Term,
        x: Term,
        y: Term,
    ) -> CheckResult<Option<(Vec<Term>, Vec<Term>, Term)>> {
        let Some((xs, nil)) = self.list_parts(f, x)? else {
            return Ok(None);
        };
        let Some((ys, other_nil)) = self.list_parts(f, y)? else {
            return Ok(None);
        };
        if other_nil != nil {
            return Ok(None);
        }
        Ok(Some((xs, ys, nil)))
    }
    fn list_concat(&mut self, f: Term, x: Term, y: Term) -> CheckResult<Term> {
        let Some((xs, ys, nil)) = self.list_pair(f, x, y)? else {
            return Ok(self.stuck());
        };
        let left = self.is_left_assoc(f)?;
        let mut both = Vec::with_capacity(xs.len() + ys.len());
        if left {
            append_terms(&mut both, &ys);
            append_terms(&mut both, &xs);
        } else {
            append_terms(&mut both, &xs);
            append_terms(&mut both, &ys);
        }
        self.list_build(f, &both, nil)
    }
    /// `list_minclude` and `list_meq`: whether the second list is included
    /// in the first as a multiset, or equal to it.
    fn list_inclusion(&mut self, op: EvalOp, f: Term, x: Term, y: Term) -> CheckResult<Term> {
        let Some((xs, ys, _)) = self.list_pair(f, x, y)? else {
            return Ok(self.stuck());
        };
        let (foreign, contained) = multiset_inclusion(&xs, &ys);
        let equality = match op {
            EvalOp::ListMeq => true,
            _ => false,
        };
        if !equality {
            return self.boolean(contained);
        }
        if foreign {
            return self.boolean(false);
        }
        if !contained {
            return self.boolean(false);
        }
        let ys = match self.list_parts(f, y)? {
            Some((ys, _)) => ys,
            None => return Err(CheckError::InvalidConstructor),
        };
        self.boolean(xs.len() == ys.len())
    }
    /// `list_inter` and `list_diff`.
    fn list_selection(&mut self, op: EvalOp, f: Term, x: Term, y: Term) -> CheckResult<Term> {
        let Some((xs, ys, nil)) = self.list_pair(f, x, y)? else {
            return Ok(self.stuck());
        };
        let paired = match op {
            EvalOp::ListInter => true,
            _ => false,
        };
        let kept = multiset_select(&xs, &ys, paired);
        self.list_build(f, &kept, nil)
    }
    /// The list operators on one list, `a[1]`.
    fn list_of_one(&mut self, op: EvalOp, f: Term, a: &[Term]) -> CheckResult<Term> {
        let Some((xs, nil)) = self.list_parts(f, a[1])? else {
            return match op {
                EvalOp::ListSingletonIntro => {
                    let nil = self.list_nil_for(f, a[1])?;
                    self.list_build(f, &[a[1]], nil)
                }
                _ => Ok(self.stuck()),
            };
        };
        match op {
            EvalOp::ListLength => self.numeral(Integer::from(xs.len())),
            EvalOp::ListNth => self.list_nth(&xs, a[2]),
            EvalOp::ListFind => self.numeral(match position(&xs, a[2]) {
                Some(i) => Integer::from(i),
                None => Integer::one().neg(),
            }),
            EvalOp::ListRev => self.list_build(f, &reversed(&xs), nil),
            EvalOp::ListSingletonElim => Ok(if xs.len() == 1 { xs[0] } else { a[1] }),
            EvalOp::ListSingletonIntro => Ok(a[1]),
            EvalOp::ListErase => self.list_build(f, &without_first(&xs, a[2]), nil),
            EvalOp::ListEraseAll => self.list_build(f, &without(&xs, a[2]), nil),
            EvalOp::ListSetof => self.list_build(f, &first_occurrences(&xs), nil),
            _ => Ok(self.stuck()),
        }
    }
    fn list_nth(&mut self, xs: &[Term], index: Term) -> CheckResult<Term> {
        Ok(match self.object_index(index)? {
            Some(n) => {
                if (n as usize) < xs.len() {
                    xs[n as usize]
                } else {
                    self.stuck()
                }
            }
            None => self.stuck(),
        })
    }
}
pub(super) fn case_2_eo__24aci_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
if v12 != v5 { return Ok(None); }
let v14 = match s.builtin_list(EvalOp::ListMeq, &[v5, v2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_3_eo__24aci_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24aci_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24aci_5fnorm_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24aci_5fnorm_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24aci_5fnorm_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24aci_5fnorm_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$aci_norm_eq"
pub fn eo__24aci_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24aci_5fnorm_5feq(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24are_5fdistinct_5fterms_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
if a1 != v2 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_0_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.builtin_core(EvalOp::IsZ, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsZ, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::And, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.builtin_core(EvalOp::IsQ, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsQ, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::And, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_2_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.builtin_core(EvalOp::IsStr, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::IsStr, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_3_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.builtin_core(EvalOp::IsBin, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsBin, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::And, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_0_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.builtin_core(EvalOp::IsBool, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsBool, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::And, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_set_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo_set_2eempty, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_0_eo__24seq_5fis_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_1_eo__24seq_5fis_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_2_eo__24seq_5fis_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24seq_5fis_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24seq_5fis_5fnon_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24seq_5fis_5fnon_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24seq_5fis_5fnon_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$seq_is_non_empty"
pub fn eo__24seq_5fis_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24seq_5fis_5fnon_5fempty(s, a0);
s.leave();
result
}
pub(super) fn if_5_eo__24seq_5fdistinct_5fterms(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match eo__24seq_5fis_5fnon_5fempty(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_6_eo__24seq_5fdistinct_5fterms(s: &mut Store, v18: Term, v2: Term) -> CheckResult<Option<Term>> {
let v21 = match if_5_eo__24seq_5fdistinct_5fterms(s, v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn if_8_eo__24seq_5fdistinct_5fterms(s: &mut Store, condition: Term, v6: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match eo__24seq_5fis_5fnon_5fempty(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_9_eo__24seq_5fdistinct_5fterms(s: &mut Store, v18: Term, v6: Term) -> CheckResult<Option<Term>> {
let v21 = match if_8_eo__24seq_5fdistinct_5fterms(s, v18, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_4_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match eo__24seq_5fis_5fnon_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_5_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match eo__24seq_5fis_5fnon_5fempty(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_6_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_1_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_1_eo__24dt_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
Ok(Some(Next::Again([a0, v1])))
}
pub(super) fn case_2_eo__24dt_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
Ok(Some(Next::Again([v1, a1])))
}
pub(super) fn case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_pattern_nat_zero(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([a0, a1, a2, v2, v4, a5])))
}
// EO program "$eo_datatype_cons_selectors_rec"
pub fn eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4, a5];
match s.cached_program(ProgramId(74), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(74), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term, mut a5: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
a3 = next[3];
a4 = next[4];
a5 = next[5];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Next<[Term; 6]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fDtSel, &[a0, a1, a2, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.native_op(NativeOp::NatSucc, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v14)))
}
pub(super) fn case_0_eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fdd_5fresolve(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, v1, v2, v3, v4, v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fdt_5fselectors_5fmain(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
Ok(s.stuck())
}
// EO program "$eo_dt_selectors_main"
pub fn eo__24eo_5fdt_5fselectors_5fmain(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdt_5fselectors_5fmain(s, a0);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fdt_5fselectors_5fmain(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fdt_5fselectors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdt_5fselectors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_dt_selectors"
pub fn eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdt_5fselectors(s, a0);
s.leave();
result
}
pub(super) fn if_2_eo__24dt_5fdistinct_5fterms(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match eo__24eo_5fdt_5fselectors(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::IsOk, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24dt_5fdistinct_5fterms(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
Some(false) => {
let v3 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::IsEq, &[a0, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_2_eo__24dt_5fdistinct_5fterms(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24dt_5fdistinct_5fterms(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match eo__24eo_5fdt_5fselectors(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::IsOk, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24dt_5fdistinct_5fterms(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IsEq, &[a1, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_4_eo__24dt_5fdistinct_5fterms(s, v14, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_6_eo__24dt_5fdistinct_5fterms(s: &mut Store, v20: Term, v21: Term, a0: Term, a1: Term) -> CheckResult<Term> {
if v20 != v21 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v20) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v22 = match s.builtin_core(EvalOp::Eq, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Not, &[v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
pub(super) fn case_3_eo__24dt_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::IsEq, &[a0, v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_3_eo__24dt_5fdistinct_5fterms(s, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsEq, &[a1, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_5_eo__24dt_5fdistinct_5fterms(s, v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::And, &[v9, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match requires_6_eo__24dt_5fdistinct_5fterms(s, v20, v21, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v24)))
}
// EO program "$are_distinct_terms_type"
pub fn eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(5), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(5), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_5_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24set_5fis_5fnot_5fsubset(s, a0, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24set_5fis_5fnot_5fsubset(s, a1, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Or, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_6_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24seq_5fdistinct_5fterms(s, a0, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_7_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24dt_5fdistinct_5fterms(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::IsOk, &[v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match if_0_eo__24are_5fdistinct_5fterms_5ftype(s, v1, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_1_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24are_5fdistinct_5fterms_5ftype(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match eo__24dt_5fdistinct_5fterms(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
Some(false) => {
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
None => Ok(s.stuck()),
}
}
// EO program "$dt_distinct_terms"
pub fn eo__24dt_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(63), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24dt_5fdistinct_5fterms(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(63), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24dt_5fdistinct_5fterms(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24dt_5fdistinct_5fterms(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24dt_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24dt_5fdistinct_5fterms(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5fdistinct_5fterms(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24dt_5fdistinct_5fterms(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24dt_5fdistinct_5fterms(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_0_eo__24dt_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match eo__24dt_5fdistinct_5fterms(s, v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_1_eo__24dt_5fdistinct_5fterms(s, v6, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn if_0_eo__24dt_5fdistinct_5fterms(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24are_5fdistinct_5fterms_5ftype(s, v2, v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24dt_5fdistinct_5fterms(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_0_eo__24dt_5fdistinct_5fterms(s, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
// EO program "$seq_distinct_terms"
pub fn eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(975), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(975), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
more_2_eo__24seq_5fdistinct_5fterms(s, v19, v9, v20, a2, v2, v13)
}
pub(super) fn case_1_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_3_eo__24seq_5fdistinct_5fterms(s, v8, v2, v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_2_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.builtin_core(EvalOp::Eq, &[v9, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_4_eo__24seq_5fdistinct_5fterms(s, v15, v9, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24seq_5fdistinct_5fterms(s, v18, v2)
}
pub(super) fn case_3_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.builtin_core(EvalOp::Eq, &[v2, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_7_eo__24seq_5fdistinct_5fterms(s, v15, v2, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24seq_5fdistinct_5fterms(s, v18, v6)
}
pub(super) fn cases_0_0_eo__24seq_5fdistinct_5fterms(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24seq_5fdistinct_5fterms(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24seq_5fdistinct_5fterms(s: &mut Store, condition: Term, v9: Term, v20: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match eo__24are_5fdistinct_5fterms_5ftype(s, v9, v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24seq_5fdistinct_5fterms(s: &mut Store, condition: Term, v2: Term, v13: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v26 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
Some(false) => {
let v27 = match eo__24seq_5fdistinct_5fterms(s, v2, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24seq_5fdistinct_5fterms(s: &mut Store, v19: Term, v9: Term, v20: Term, a2: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v21 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.builtin_core(EvalOp::Eq, &[v9, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_0_eo__24seq_5fdistinct_5fterms(s, v22, v9, v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_1_eo__24seq_5fdistinct_5fterms(s, v25, v2, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn if_3_eo__24seq_5fdistinct_5fterms(s: &mut Store, condition: Term, v2: Term, v6: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24are_5fdistinct_5fterms_5ftype(s, v2, v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24seq_5fdistinct_5fterms(s: &mut Store, condition: Term, v9: Term, v13: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match eo__24are_5fdistinct_5fterms_5ftype(s, v9, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24seq_5fdistinct_5fterms(s: &mut Store, condition: Term, v2: Term, v13: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match eo__24are_5fdistinct_5fterms_5ftype(s, v2, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
// EO program "$set_is_not_subset"
pub fn eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(984), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(984), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_0_eo__24set_5fis_5fnot_5fsubset(s, v8, v2, v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_3_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.builtin_core(EvalOp::Eq, &[v2, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_1_eo__24set_5fis_5fnot_5fsubset(s, v15, v2, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24set_5fis_5fnot_5fsubset(s, v18, v2, v6, a2)
}
pub(super) fn case_4_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24set_5fis_5fnot_5fsubset(s, v12, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_4_eo__24set_5fis_5fnot_5fsubset(s, v13, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn cases_0_0_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24set_5fis_5fnot_5fsubset(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, condition: Term, v2: Term, v6: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24are_5fdistinct_5fterms_5ftype(s, v2, v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, condition: Term, v2: Term, v13: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match eo__24are_5fdistinct_5fterms_5ftype(s, v2, v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, condition: Term, v2: Term, v6: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24set_5fis_5fnot_5fsubset(s, v20, v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
Some(false) => {
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_3_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, v18: Term, v2: Term, v6: Term, a2: Term) -> CheckResult<Option<Term>> {
let v23 = match if_2_eo__24set_5fis_5fnot_5fsubset(s, v18, v2, v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn if_4_eo__24set_5fis_5fnot_5fsubset(s: &mut Store, condition: Term, v2: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v14 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match eo__24set_5fis_5fnot_5fsubset(s, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24are_5fdistinct_5fterms_5flist_5frec(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match eo__24are_5fdistinct_5fterms_5ftype(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24are_5fdistinct_5fterms_5flist_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
if a2 != v2 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$are_distinct_terms_list_rec"
pub fn eo__24are_5fdistinct_5fterms_5flist_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(4), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24are_5fdistinct_5fterms_5flist_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(4), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24are_5fdistinct_5fterms_5flist_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24are_5fdistinct_5fterms_5flist_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24are_5fdistinct_5fterms_5flist_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24are_5fdistinct_5fterms_5flist_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::Eq, &[a0, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24are_5fdistinct_5fterms_5flist_5frec(s, v7, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_1_eo__24are_5fdistinct_5fterms_5flist_5frec(s, v10, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn if_1_eo__24are_5fdistinct_5fterms_5flist_5frec(s: &mut Store, condition: Term, a0: Term, v2: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24are_5fdistinct_5fterms_5flist_5frec(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
// EO program "$are_distinct_terms_list"
pub fn eo__24are_5fdistinct_5fterms_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(3), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24are_5fdistinct_5fterms_5flist(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(3), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24are_5fdistinct_5fterms_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24are_5fdistinct_5fterms_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24are_5fdistinct_5fterms_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24are_5fdistinct_5fterms_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24are_5fdistinct_5fterms_5flist_5frec(s, v5, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24are_5fdistinct_5fterms_5flist(s, v7, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn if_0_eo__24are_5fdistinct_5fterms_5flist(s: &mut Store, condition: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24are_5fdistinct_5fterms_5flist(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24arith_5fnormalize_5flit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24arith_5frel_5fneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24arith_5frel_5fneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_2_eo__24arith_5frel_5fneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_3_eo__24arith_5frel_5fneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24arith_5frel_5fneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24arith_5frel_5fneg(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24arith_5frel_5fneg(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24arith_5frel_5fneg(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24arith_5frel_5fneg(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_rel_neg"
pub fn eo__24arith_5frel_5fneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5frel_5fneg(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_1_eo__24arith_5fnormalize_5flit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match eo__24arith_5frel_5fneg(s, v8, v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_2_eo__24arith_5fnormalize_5flit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24arith_5fnormalize_5flit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24arith_5fnormalize_5flit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24arith_5fnormalize_5flit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24arith_5fnormalize_5flit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_normalize_lit"
pub fn eo__24arith_5fnormalize_5flit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5fnormalize_5flit(s, a0);
s.leave();
result
}
pub(super) fn more_3_eo__24arith_5freduction_5fpred(s: &mut Store, v48: Term, v50: Term, v37: Term, v36: Term, v20: Term, v19: Term) -> CheckResult<Option<Term>> {
let v51 = match s.apply(v48, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v37, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v36, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v20, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v56, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v19, v58) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v59))
}
pub(super) fn more_2_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v37: Term, v36: Term, v20: Term, v19: Term) -> CheckResult<Option<Term>> {
let v38 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v42, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v41, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v40, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v38, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v50 = match s.literal(Lit::Rational(v49)) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24arith_5freduction_5fpred(s, v48, v50, v37, v36, v20, v19)
}
pub(super) fn more_1_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v25: Term, v21: Term, v20: Term, v19: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v28, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v27, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v25, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v21, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24arith_5freduction_5fpred(s, v2, v37, v36, v20, v19)
}
pub(super) fn more_0_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v12: Term, v11: Term, v10: Term, v8: Term, v4: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v10, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v8, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v4, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v24 = match s.literal(Lit::Rational(v23)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24arith_5freduction_5fpred(s, v2, v25, v21, v20, v19)
}
pub(super) fn case_0_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_is_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_is_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24arith_5freduction_5fpred(s, v2, v12, v11, v10, v8, v4)
}
pub(super) fn more_7_eo__24arith_5freduction_5fpred(s: &mut Store, v15: Term, v50: Term, v14: Term) -> CheckResult<Option<Term>> {
let v51 = match s.apply(v15, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v51, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v14, v53) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v54))
}
pub(super) fn more_6_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v37: Term, v36: Term, v35: Term, v33: Term, v32: Term, v31: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v38 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v37, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v36, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v35, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v33, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v45 = match s.literal(Lit::Rational(v44)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v32, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v31, v49) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24arith_5freduction_5fpred(s, v15, v50, v14)
}
pub(super) fn more_5_eo__24arith_5freduction_5fpred(s: &mut Store, v25: Term, v2: Term, v24: Term, v23: Term, v22: Term, v20: Term, v16: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v23, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v22, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v20, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v16, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24arith_5freduction_5fpred(s, v2, v37, v36, v35, v33, v32, v31, v15, v14)
}
pub(super) fn more_4_eo__24arith_5freduction_5fpred(s: &mut Store, v8: Term, v12: Term, v4: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v4, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v19 = match s.literal(Lit::Rational(v18)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24arith_5freduction_5fpred(s, v25, v2, v24, v23, v22, v20, v16, v15, v14)
}
pub(super) fn case_1_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24arith_5freduction_5fpred(s, v8, v12, v4, v2)
}
pub(super) fn if_8_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_10_eo__24arith_5freduction_5fpred(s: &mut Store, v28: Term, v5: Term, v2: Term, v27: Term, v11: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v27, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v11, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn more_9_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v14: Term, v12: Term, v5: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24arith_5fmk_5fzero(s, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v12, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__40div_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Eq, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_8_eo__24arith_5freduction_5fpred(s, v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v18, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24arith_5freduction_5fpred(s, v28, v5, v2, v27, v11)
}
pub(super) fn case_2_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24arith_5freduction_5fpred(s, v2, v14, v12, v5, v11)
}
pub(super) fn more_11_eo__24arith_5freduction_5fpred(s: &mut Store, v14: Term, v12: Term, v5: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40int_5fdiv_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v11, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_3_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_div, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24arith_5freduction_5fpred(s, v14, v12, v5, v2, v11)
}
pub(super) fn cases_0_0_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_12_eo__24arith_5freduction_5fpred(s: &mut Store, v14: Term, v12: Term, v5: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40mod_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v11, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_4_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24arith_5freduction_5fpred(s, v14, v12, v5, v2, v11)
}
pub(super) fn if_13_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
Some(false) => {
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v41 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
Some(false) => {
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v56 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
Some(false) => {
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v67 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v68)
}
Some(false) => {
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_21_eo__24arith_5freduction_5fpred(s: &mut Store, v20: Term, v71: Term, v19: Term) -> CheckResult<Option<Term>> {
let v72 = match s.apply(v20, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v72, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v19, v74) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v75))
}
pub(super) fn more_20_eo__24arith_5freduction_5fpred(s: &mut Store, v55: Term, v2: Term, v52: Term, v51: Term, v44: Term, v36: Term, v5: Term, v35: Term, v20: Term, v19: Term) -> CheckResult<Option<Term>> {
let v58 = match if_15_eo__24arith_5freduction_5fpred(s, v55, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24eo_5ftypeof(s, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24eo_5fnil(s, v52, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v51, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v44, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v36, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_core(EvalOp::Eq, &[v64, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match if_16_eo__24arith_5freduction_5fpred(s, v66, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v63, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v35, v70) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24arith_5freduction_5fpred(s, v20, v71, v19)
}
pub(super) fn more_19_eo__24arith_5freduction_5fpred(s: &mut Store, v37: Term, v43: Term, v5: Term, v2: Term, v36: Term, v35: Term, v20: Term, v19: Term) -> CheckResult<Option<Term>> {
let v44 = match s.apply(v37, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v46, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v45, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_core(EvalOp::Eq, &[v53, v54]) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24arith_5freduction_5fpred(s, v55, v2, v52, v51, v44, v36, v5, v35, v20, v19)
}
pub(super) fn more_18_eo__24arith_5freduction_5fpred(s: &mut Store, v26: Term, v2: Term, v23: Term, v22: Term, v21: Term, v5: Term, v20: Term, v19: Term) -> CheckResult<Option<Term>> {
let v29 = match if_13_eo__24arith_5freduction_5fpred(s, v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v23, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v32 = match s.literal(Lit::Rational(v31)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v22, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v21, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Eq, &[v38, v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match if_14_eo__24arith_5freduction_5fpred(s, v40, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24arith_5freduction_5fpred(s, v37, v43, v5, v2, v36, v35, v20, v19)
}
pub(super) fn more_17_eo__24arith_5freduction_5fpred(s: &mut Store, v14: Term, v5: Term, v2: Term, v13: Term, v12: Term, v7: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v12, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v7, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::Eq, &[v24, v25]) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24arith_5freduction_5fpred(s, v26, v2, v23, v22, v21, v5, v20, v19)
}
pub(super) fn case_5_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24arith_5freduction_5fpred(s, v14, v5, v2, v13, v12, v7)
}
pub(super) fn if_22_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v57 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
Some(false) => {
let v58 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v58)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_25_eo__24arith_5freduction_5fpred(s: &mut Store, v54: Term, v62: Term, v47: Term, v46: Term, v44: Term, v42: Term, v41: Term) -> CheckResult<Term> {
let v63 = match s.apply(v54, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v47, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v64, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v46, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v44, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v42, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v69, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v41, v71) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v72)
}
pub(super) fn more_24_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v48: Term, v47: Term, v46: Term, v44: Term, v42: Term, v41: Term) -> CheckResult<Term> {
let v49 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v49, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v48, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match if_22_eo__24arith_5freduction_5fpred(s, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v55, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v60, v61) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24arith_5freduction_5fpred(s, v54, v62, v47, v46, v44, v42, v41)
}
pub(super) fn more_23_eo__24arith_5freduction_5fpred(s: &mut Store, v35: Term, v36: Term, v28: Term, v26: Term, v5: Term, v25: Term, v2: Term) -> CheckResult<Term> {
let v37 = match s.apply(v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v28, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v26, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v25, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24arith_5freduction_5fpred(s, v5, v2, v48, v47, v46, v44, v42, v41)
}
pub(super) fn requires_26_eo__24arith_5freduction_5fpred(s: &mut Store, v23: Term, v24: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v23 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v23) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v25 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v29, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24arith_5freduction_5fpred(s, v35, v36, v28, v26, v5, v25, v2)
}
pub(super) fn more_35_eo__24arith_5freduction_5fpred(s: &mut Store, v181: Term, v127: Term) -> CheckResult<Term> {
let v182 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v181, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v127, v183) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v184)
}
pub(super) fn more_34_eo__24arith_5freduction_5fpred(s: &mut Store, v164: Term, v169: Term, v157: Term, v156: Term, v154: Term, v152: Term, v151: Term, v134: Term, v128: Term, v127: Term) -> CheckResult<Term> {
let v170 = match s.apply(v164, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v157, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v171, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v156, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v154, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v152, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v176, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v151, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v134, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v128, v180) { Ok(v) => v, Err(e) => return Err(e) };
more_35_eo__24arith_5freduction_5fpred(s, v181, v127)
}
pub(super) fn more_33_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v157: Term, v156: Term, v154: Term, v152: Term, v151: Term, v134: Term, v128: Term, v127: Term) -> CheckResult<Term> {
let v158 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v161, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v159, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v158, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v165, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v167, v168) { Ok(v) => v, Err(e) => return Err(e) };
more_34_eo__24arith_5freduction_5fpred(s, v164, v169, v157, v156, v154, v152, v151, v134, v128, v127)
}
pub(super) fn more_32_eo__24arith_5freduction_5fpred(s: &mut Store, v145: Term, v138: Term, v136: Term, v5: Term, v135: Term, v2: Term, v134: Term, v128: Term, v127: Term) -> CheckResult<Term> {
let v146 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v145, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v138, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v136, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v135, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v153, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_33_eo__24arith_5freduction_5fpred(s, v5, v2, v157, v156, v154, v152, v151, v134, v128, v127)
}
pub(super) fn more_31_eo__24arith_5freduction_5fpred(s: &mut Store, v129: Term, v133: Term, v2: Term, v5: Term, v128: Term, v127: Term) -> CheckResult<Term> {
let v134 = match s.apply(v129, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v142, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v140, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v139, v144) { Ok(v) => v, Err(e) => return Err(e) };
more_32_eo__24arith_5freduction_5fpred(s, v145, v138, v136, v5, v135, v2, v134, v128, v127)
}
pub(super) fn more_30_eo__24arith_5freduction_5fpred(s: &mut Store, v98: Term, v121: Term, v97: Term, v80: Term, v74: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let v122 = match s.apply(v98, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v122, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v97, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v80, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v74, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v131, v132) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24arith_5freduction_5fpred(s, v129, v133, v2, v5, v128, v127)
}
pub(super) fn more_29_eo__24arith_5freduction_5fpred(s: &mut Store, v104: Term, v109: Term, v103: Term, v102: Term, v100: Term, v98: Term, v97: Term, v80: Term, v74: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let v110 = match s.apply(v104, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v111, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v110, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v103, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v117, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v102, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v100, v120) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24arith_5freduction_5fpred(s, v98, v121, v97, v80, v74, v2, v5)
}
pub(super) fn more_28_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v97: Term, v80: Term, v74: Term) -> CheckResult<Term> {
let v98 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v105, v108) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24arith_5freduction_5fpred(s, v104, v109, v103, v102, v100, v98, v97, v80, v74, v2, v5)
}
pub(super) fn more_27_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v85: Term, v84: Term, v82: Term, v81: Term, v80: Term, v74: Term) -> CheckResult<Term> {
let v86 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v86, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v85, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v91, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v84, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v82, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v81, v96) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24arith_5freduction_5fpred(s, v5, v2, v97, v80, v74)
}
pub(super) fn if_36_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v22 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v2, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match requires_26_eo__24arith_5freduction_5fpred(s, v23, v24, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v73)
}
Some(false) => {
let v74 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v77, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v75, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24arith_5freduction_5fpred(s, v5, v2, v85, v84, v82, v81, v80, v74)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_37_eo__24arith_5freduction_5fpred(s: &mut Store, v14: Term, v5: Term, v2: Term, v13: Term, v12: Term, v7: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v12, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v7, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::IsZ, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match if_36_eo__24arith_5freduction_5fpred(s, v21, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v20, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v186, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v19, v188) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v189))
}
pub(super) fn case_6_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_37_eo__24arith_5freduction_5fpred(s, v14, v5, v2, v13, v12, v7)
}
pub(super) fn if_38_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v67 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v67)
}
Some(false) => {
let v68 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v68)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_41_eo__24arith_5freduction_5fpred(s: &mut Store, v64: Term, v72: Term, v57: Term, v56: Term, v54: Term, v52: Term, v51: Term) -> CheckResult<Term> {
let v73 = match s.apply(v64, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v57, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v74, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v56, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v54, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v52, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v79, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v51, v81) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v82)
}
pub(super) fn more_40_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v58: Term, v57: Term, v56: Term, v54: Term, v52: Term, v51: Term) -> CheckResult<Term> {
let v59 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v59, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v58, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match if_38_eo__24arith_5freduction_5fpred(s, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v65, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v70, v71) { Ok(v) => v, Err(e) => return Err(e) };
more_41_eo__24arith_5freduction_5fpred(s, v64, v72, v57, v56, v54, v52, v51)
}
pub(super) fn more_39_eo__24arith_5freduction_5fpred(s: &mut Store, v45: Term, v46: Term, v38: Term, v36: Term, v5: Term, v35: Term, v2: Term) -> CheckResult<Term> {
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v38, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v36, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v35, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_40_eo__24arith_5freduction_5fpred(s, v5, v2, v58, v57, v56, v54, v52, v51)
}
pub(super) fn requires_42_eo__24arith_5freduction_5fpred(s: &mut Store, v33: Term, v34: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v33 != v34 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v33) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v35 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v39, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_39_eo__24arith_5freduction_5fpred(s, v45, v46, v38, v36, v5, v35, v2)
}
pub(super) fn more_51_eo__24arith_5freduction_5fpred(s: &mut Store, v191: Term, v137: Term) -> CheckResult<Term> {
let v192 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v191, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v137, v193) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v194)
}
pub(super) fn more_50_eo__24arith_5freduction_5fpred(s: &mut Store, v174: Term, v179: Term, v167: Term, v166: Term, v164: Term, v162: Term, v161: Term, v144: Term, v138: Term, v137: Term) -> CheckResult<Term> {
let v180 = match s.apply(v174, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v167, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v181, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v166, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v164, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v162, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v186, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v161, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v144, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v138, v190) { Ok(v) => v, Err(e) => return Err(e) };
more_51_eo__24arith_5freduction_5fpred(s, v191, v137)
}
pub(super) fn more_49_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v167: Term, v166: Term, v164: Term, v162: Term, v161: Term, v144: Term, v138: Term, v137: Term) -> CheckResult<Term> {
let v168 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v169, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v168, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v175, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v177, v178) { Ok(v) => v, Err(e) => return Err(e) };
more_50_eo__24arith_5freduction_5fpred(s, v174, v179, v167, v166, v164, v162, v161, v144, v138, v137)
}
pub(super) fn more_48_eo__24arith_5freduction_5fpred(s: &mut Store, v155: Term, v148: Term, v146: Term, v5: Term, v145: Term, v2: Term, v144: Term, v138: Term, v137: Term) -> CheckResult<Term> {
let v156 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v155, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v148, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v146, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v159, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v145, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v163, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v165, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_49_eo__24arith_5freduction_5fpred(s, v5, v2, v167, v166, v164, v162, v161, v144, v138, v137)
}
pub(super) fn more_47_eo__24arith_5freduction_5fpred(s: &mut Store, v139: Term, v143: Term, v2: Term, v5: Term, v138: Term, v137: Term) -> CheckResult<Term> {
let v144 = match s.apply(v139, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v147, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v151, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v152, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v150, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v149, v154) { Ok(v) => v, Err(e) => return Err(e) };
more_48_eo__24arith_5freduction_5fpred(s, v155, v148, v146, v5, v145, v2, v144, v138, v137)
}
pub(super) fn more_46_eo__24arith_5freduction_5fpred(s: &mut Store, v108: Term, v131: Term, v107: Term, v90: Term, v84: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let v132 = match s.apply(v108, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v132, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v107, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v90, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v84, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v140, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v141, v142) { Ok(v) => v, Err(e) => return Err(e) };
more_47_eo__24arith_5freduction_5fpred(s, v139, v143, v2, v5, v138, v137)
}
pub(super) fn more_45_eo__24arith_5freduction_5fpred(s: &mut Store, v114: Term, v119: Term, v113: Term, v112: Term, v110: Term, v108: Term, v107: Term, v90: Term, v84: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let v120 = match s.apply(v114, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v121, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v123, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v120, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v113, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v127, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v112, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v110, v130) { Ok(v) => v, Err(e) => return Err(e) };
more_46_eo__24arith_5freduction_5fpred(s, v108, v131, v107, v90, v84, v2, v5)
}
pub(super) fn more_44_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v107: Term, v90: Term, v84: Term) -> CheckResult<Term> {
let v108 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v116, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v115, v118) { Ok(v) => v, Err(e) => return Err(e) };
more_45_eo__24arith_5freduction_5fpred(s, v114, v119, v113, v112, v110, v108, v107, v90, v84, v2, v5)
}
pub(super) fn more_43_eo__24arith_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v95: Term, v94: Term, v92: Term, v91: Term, v90: Term, v84: Term) -> CheckResult<Term> {
let v96 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v98, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v96, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v95, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v101, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v94, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v92, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v91, v106) { Ok(v) => v, Err(e) => return Err(e) };
more_44_eo__24arith_5freduction_5fpred(s, v5, v2, v107, v90, v84)
}
pub(super) fn if_52_eo__24arith_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v32 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::Eq, &[v2, v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match requires_42_eo__24arith_5freduction_5fpred(s, v33, v34, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v83)
}
Some(false) => {
let v84 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v86, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v87, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v85, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_43_eo__24arith_5freduction_5fpred(s, v5, v2, v95, v94, v92, v91, v90, v84)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_54_eo__24arith_5freduction_5fpred(s: &mut Store, v14: Term, v26: Term, v12: Term, v7: Term, v2: Term, v5: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v14, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v12, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v7, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::IsZ, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match if_52_eo__24arith_5freduction_5fpred(s, v31, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v30, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v196, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v29, v198) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v199))
}
pub(super) fn more_53_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v5: Term, v14: Term, v12: Term, v7: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v17, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_54_eo__24arith_5freduction_5fpred(s, v14, v26, v12, v7, v2, v5)
}
pub(super) fn case_7_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_53_eo__24arith_5freduction_5fpred(s, v2, v5, v14, v12, v7)
}
pub(super) fn cases_0_1_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_55_eo__24arith_5freduction_5fpred(s: &mut Store, v10: Term, v12: Term, v8: Term, v2: Term, v7: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v7, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_8_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24arith_5fmk_5fzero(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_55_eo__24arith_5freduction_5fpred(s, v10, v12, v8, v2, v7)
}
pub(super) fn more_61_eo__24arith_5freduction_5fpred(s: &mut Store, v72: Term, v66: Term, v58: Term, v57: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v73 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v72, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v66, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v58, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v76, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v57, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v15, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v14, v82) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v83))
}
pub(super) fn more_60_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v60: Term, v59: Term, v58: Term, v57: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v61 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v61, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v60, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v59, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v67, v71) { Ok(v) => v, Err(e) => return Err(e) };
more_61_eo__24arith_5freduction_5fpred(s, v72, v66, v58, v57, v15, v14)
}
pub(super) fn more_59_eo__24arith_5freduction_5fpred(s: &mut Store, v43: Term, v48: Term, v37: Term, v36: Term, v34: Term, v33: Term, v22: Term, v16: Term, v2: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v49 = match s.apply(v43, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v37, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v36, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v34, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v33, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v22, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v16, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_60_eo__24arith_5freduction_5fpred(s, v2, v60, v59, v58, v57, v15, v14)
}
pub(super) fn more_58_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v36: Term, v34: Term, v33: Term, v22: Term, v16: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v37 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v38, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v46, v47) { Ok(v) => v, Err(e) => return Err(e) };
more_59_eo__24arith_5freduction_5fpred(s, v43, v48, v37, v36, v34, v33, v22, v16, v2, v15, v14)
}
pub(super) fn more_57_eo__24arith_5freduction_5fpred(s: &mut Store, v2: Term, v24: Term, v23: Term, v22: Term, v16: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v25 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v24, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v23, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_58_eo__24arith_5freduction_5fpred(s, v2, v36, v34, v33, v22, v16, v15, v14)
}
