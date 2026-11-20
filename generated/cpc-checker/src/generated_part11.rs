//! Generated functions, module 11 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn case_2_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24get_5fai_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_3_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24get_5fai_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn cases_0_0_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24get_5fai_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_5_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24get_5fai_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_1_eo__24get_5fa_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if a2 != a1 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn case_2_eo__24get_5fa_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.apply(a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$get_a_norm_rec"
pub fn eo__24get_5fa_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(875), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5fa_5fnorm_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(875), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24get_5fa_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5fa_5fnorm_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24get_5fa_5fnorm_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24get_5fa_5fnorm_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24get_5fa_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match eo__24get_5fa_5fnorm_5frec(s, a0, a1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24get_5fa_5fnorm_5frec(s, a0, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListConcat, &[a0, v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24get_5fa_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fnil(s, v4, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24get_5fa_5fnorm_5frec(s, v4, v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonElim, &[v4, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24get_5fa_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5fa_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$get_a_norm"
pub fn eo__24get_5fa_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24get_5fa_5fnorm(s, a0);
s.leave();
result
}
pub(super) fn case_6_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24get_5fa_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_7_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24get_5fa_5fnorm(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn cases_0_1_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_8_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24get_5fa_5fnorm(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_9_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24get_5fa_5fnorm(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_10_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
Ok(Some(a0))
}
pub(super) fn cases_0_2_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24get_5faci_5fnormal_5fform(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$get_aci_normal_form"
pub fn eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24get_5faci_5fnormal_5fform(s, a0);
s.leave();
result
}
pub(super) fn if_0_eo__24eo_5fprog_5faci_5fnorm(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match eo__24get_5faci_5fnormal_5fform(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24get_5faci_5fnormal_5fform(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24aci_5fnorm_5feq(s, v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5faci_5fnorm(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24get_5faci_5fnormal_5fform(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24aci_5fnorm_5feq(s, v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_0_eo__24eo_5fprog_5faci_5fnorm(s, v11, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_2_eo__24eo_5fprog_5faci_5fnorm(s: &mut Store, v17: Term, v18: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
pub(super) fn case_0_eo__24eo_5fprog_5faci_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5faci_5fnormal_5fform(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24aci_5fnorm_5feq(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_1_eo__24eo_5fprog_5faci_5fnorm(s, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match requires_2_eo__24eo_5fprog_5faci_5fnorm(s, v17, v18, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn body_eo__24eo_5fprog_5faci_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5faci_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_aci_norm"
pub fn eo__24eo_5fprog_5faci_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5faci_5fnorm(s, a0);
s.leave();
result
}
pub(super) fn case_607_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eaci_5fnorm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fprog_5faci_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_151_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_604_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_605_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_606_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_607_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_37_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_148_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_149_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_150_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_151_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fabsorb(s: &mut Store, v8: Term, v9: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v8 != v9 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v8) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
pub(super) fn case_0_eo__24is_5fabsorb_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if a2 != a1 { return Ok(None); }
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn case_2_eo__24is_5fabsorb_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$is_absorb_rec"
pub fn eo__24is_5fabsorb_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(889), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fabsorb_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(889), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24is_5fabsorb_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5fabsorb_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fabsorb_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24is_5fabsorb_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24is_5fabsorb_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match eo__24is_5fabsorb_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_0_eo__24is_5fabsorb_5frec(s, v6, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn if_0_eo__24is_5fabsorb_5frec(s: &mut Store, condition: Term, a0: Term, v2: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match eo__24is_5fabsorb_5frec(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24is_5fabsorb(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24is_5fabsorb_5frec(s, v4, v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24is_5fabsorb(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5fabsorb(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_absorb"
pub fn eo__24is_5fabsorb(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5fabsorb(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_1_eo__24eo_5fprog_5fabsorb(s: &mut Store, v7: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v7 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match eo__24is_5fabsorb(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match requires_0_eo__24eo_5fprog_5fabsorb(s, v8, v9, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
pub(super) fn case_0_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_2_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_3_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn cases_0_0_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn if_0_eo__24get_5fzero(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fbitwidth(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Pow, &[v16, v18]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24get_5fzero(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IsNeg, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_0_eo__24get_5fzero(s, v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24bv_5fbitwidth(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24get_5fzero(s: &mut Store, v8: Term, v27: Term) -> CheckResult<Option<Term>> {
let v28 = match s.builtin_core(EvalOp::ToBin, &[v8, v27]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_5_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitwidth(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsZ, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_1_eo__24get_5fzero(s, v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Add, &[v25, v26]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24get_5fzero(s, v8, v27)
}
pub(super) fn case_6_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitwidth(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToBin, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn cases_0_1_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24get_5fzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$get_zero"
pub fn eo__24get_5fzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24get_5fzero(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fabsorb(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5fzero(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match requires_1_eo__24eo_5fprog_5fabsorb(s, v7, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn body_eo__24eo_5fprog_5fabsorb(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fabsorb(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_absorb"
pub fn eo__24eo_5fprog_5fabsorb(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fabsorb(s, a0);
s.leave();
result
}
pub(super) fn case_608_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eabsorb, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fprog_5fabsorb(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s: &mut Store, v18: Term, v19: Term, v9: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn more_1_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s: &mut Store, v14: Term, v9: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24assoc_5fnil_5fnth_5ftype(s, v14, v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24compute_5fcard(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Gt, &[v13, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match requires_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s, v18, v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListLength, &[v12, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s, v14, v9, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_distinct-card-conflict"
pub fn eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s, a0);
s.leave();
result
}
pub(super) fn case_609_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edistinct_5fcard_5fconflict, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fprog_5fdistinct_2dcard_2dconflict(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_610_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_152_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_608_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_609_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_610_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_38_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_152_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_9_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_36_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_37_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_38_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_3_2_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_2_8_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_2_9_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match cases_3_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_3_1_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_3_2_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_cmd_step_proven"
pub fn eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fpush_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fis_5fbool_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5fpush_5fproven_5fcheck(s, v0, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fpush_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fpush_5fproven(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_push_proven"
pub fn eo__24eo_5fpush_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fpush_5fproven(s, a0, a1);
s.leave();
result
}
pub(super) fn case_3_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmd_2estep, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fcmd_5fstep_5fproven(s, a0, v1, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fpush_5fproven(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_0_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5fprog_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fscope(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_scope"
pub fn eo__24eo_5fprog_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fscope(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2escope, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fscope(s, a3, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_cmd_step_pop_proven"
pub fn eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fso_2eassume_5fpush, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a2, a3, v4, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fpush_5fproven(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([a0, v2, a2, a3, a4])))
}
pub(super) fn case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Next<[Term; 5]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
a3 = next[3];
a4 = next[4];
}
Err(e) => return Err(e),
}
}
}
// EO program "$eo_invoke_cmd_step_pop"
pub fn eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmd_2estep_5fpop, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a0, v1, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_1_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match cases_0_0_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_invoke_cmd"
pub fn eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fcmd(s, a0, a1);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmdl_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5finvoke_5fcmd(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v3, v2])))
}
pub(super) fn step_eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$eo_invoke_cmd_list"
pub fn eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fso_2eassume_5fpush, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_1_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([v2])))
}
pub(super) fn case_2_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_3_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5fstate_5fis_5fclosed(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
// EO program "$eo_state_is_closed"
pub fn eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fstate_5fis_5fclosed(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fstate_5fis_5frefutation(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s, a0, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5fstate_5fis_5fclosed(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fstate_5fis_5frefutation(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fstate_5fis_5frefutation(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_state_is_refutation"
pub fn eo__24eo_5fstate_5fis_5frefutation(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fstate_5fis_5frefutation(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fchecker_5fis_5frefutation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5finvoke_5fassume_5flist(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5finvoke_5fcmd_5flist(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fstate_5fis_5frefutation(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fchecker_5fis_5frefutation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fchecker_5fis_5frefutation(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_checker_is_refutation"
pub fn eo__24eo_5fchecker_5fis_5frefutation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fchecker_5fis_5frefutation(s, a0, a1);
s.leave();
result
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dall_2delim(s: &mut Store) -> CheckResult<Term> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
// EO program "$eo_prog_re-all-elim"
pub fn eo__24eo_5fprog_5fre_2dall_2delim(s: &mut Store) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dall_2delim(s);
s.leave();
result
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dstar_2demp(s: &mut Store) -> CheckResult<Term> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
// EO program "$eo_prog_re-star-emp"
pub fn eo__24eo_5fprog_5fre_2dstar_2demp(s: &mut Store) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dstar_2demp(s);
s.leave();
result
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dstar_2dnone(s: &mut Store) -> CheckResult<Term> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
// EO program "$eo_prog_re-star-none"
pub fn eo__24eo_5fprog_5fre_2dstar_2dnone(s: &mut Store) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dstar_2dnone(s);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5ftrust(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(a0))
}
pub(super) fn body_eo__24eo_5fprog_5ftrust(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5ftrust(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_trust"
pub fn eo__24eo_5fprog_5ftrust(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5ftrust(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBoolean, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eBoolean, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fRational, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eRational, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_3_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fString, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eString, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn cases_0_0_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBinary, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.native_op(NativeOp::StringPrefixEq, &[v0, a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_reserved_datatype_name"
pub fn eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn if_1_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eTypeRef, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDatatypeTypeRef, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_1_eo__24eo_5fto_5fsmt_5ftype(s, v2, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fguard(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
Some(false) => {
Ok(a1)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fguard(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.native_op(NativeOp::Teq, &[a0, v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24smtx_5ftypeof_5fguard(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fguard(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fguard(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_guard"
pub fn eo__24smtx_5ftypeof_5fguard(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fguard(s, a0, a1);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUSort, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eUSort, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_6_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_7_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn if_2_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.native_op(NativeOp::IntToNat, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_8_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24emb_5fNumeral, v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zleq, &[v6, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_2_eo__24eo_5fto_5fsmt_5ftype(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_9_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_12_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_13_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fdd_2econs, &[v2, v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__24emb_5fdd_2econs, &[v0, a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_tuple_decl"
pub fn eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, a0);
s.leave();
result
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s: &mut Store, condition: Term, a0: Term, v8: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[a0, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v19, v23]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_1_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([v2])))
}
pub(super) fn case_2_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_3_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn case_4_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_5_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn cases_0_1_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_4_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$smtx_decl_inhabited"
pub fn eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(973), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdecl_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(973), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdecl_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdecl_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5fdecl_5finhabited(s, v4, v2, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn if_0_eo__24smtx_5fdecl_5finhabited(s: &mut Store, condition: Term, v2: Term, v3: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match eo__24smtx_5fdt_5finhabited(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match eo__24smtx_5fdecl_5finhabited(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
// EO program "$smtx_dt_cons_inhabited"
pub fn eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(975), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(975), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24smtx_5fdecl_5finhabited(s, v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdt_5fcons_5finhabited(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5fcons_5finhabited(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$smtx_dt_inhabited"
pub fn eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(977), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(977), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdt_5fcons_5finhabited(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5finhabited(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Or, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$smtx_inhabited_type"
pub fn eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(983), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5finhabited_5ftype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(983), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5finhabited_5ftype(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5finhabited_5ftype(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match cases_0_0_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_2_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdecl_5finhabited(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn cases_0_0_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_0_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dd_has_dt"
pub fn eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(971), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdd_5fhas_5fdt(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(971), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdd_5fhas_5fdt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdd_5fhas_5fdt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5fdd_5fhas_5fdt(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Or, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_6_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_7_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eFunType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_8_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_9_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_2_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$smtx_decl_wf_rec"
pub fn eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(974), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdecl_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(974), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdecl_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdecl_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5fdt_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5finhabited_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5fdecl_5fwf_5frec(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5fdd_5fhas_5fdt(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::Not, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::And, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.native_op(NativeOp::And, &[v6, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.native_op(NativeOp::And, &[v4, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
// EO program "$smtx_dt_cons_wf_rec"
pub fn eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(976), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(976), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24smtx_5fdd_5fhas_5fdt(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
// EO program "$smtx_dt_wf_rec"
pub fn eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(980), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(980), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$smtx_type_wf_rec"
pub fn eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(988), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftype_5fwf_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(988), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match cases_0_0_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5finhabited_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftype_5fwf_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::And, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::And, &[v5, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_3_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::And, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_4_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::And, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_5_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdd_5fhas_5fdt(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdecl_5fwf_5frec(s, v2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_0_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24smtx_5ftype_5fwf_5fcomponent(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.native_op(NativeOp::And, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24smtx_5ftype_5fwf_5fcomponent(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftype_5fwf_5fcomponent(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_type_wf_component"
pub fn eo__24smtx_5ftype_5fwf_5fcomponent(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftype_5fwf_5fcomponent(s, a0);
s.leave();
result
}
pub(super) fn more_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s: &mut Store, a0: Term, v16: Term, v8: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24smtx_5ftype_5fwf_5fcomponent(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.native_op(NativeOp::And, &[v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s, v18, a0, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = fields[1];
let v10 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v11 { return Ok(None); }
let v12 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Streq, &[v1, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.native_op(NativeOp::Streq, &[v4, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.native_op(NativeOp::And, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s, a0, v16, v8)
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_type_tuple"
pub fn eo__24eo_5fto_5fsmt_5ftype_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5ftype_5ftuple(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5ftype_5fwf_5fcomponent(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$smtx_type_wf"
pub fn eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(986), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftype_5fwf(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(986), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eFunType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftype_5fwf_5fcomponent(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftype_5fwf(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_16_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_4_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$eo_to_smt_datatype"
pub fn eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(740), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(740), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdatatype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdatatype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5fdatatype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$eo_to_smt_datatype_cons"
pub fn eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(741), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(741), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$eo_to_smt_datatype_decl"
pub fn eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(742), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(742), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedd_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fto_5fsmt_5fdatatype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fdd_2econs, &[v1, v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
// EO program "$eo_to_smt_type"
pub fn eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(762), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5ftype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(762), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match cases_1_0_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_1_1_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDatatypeType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24eo_5fto_5fsmt_5ftype(s, v3, v2, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_3_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eDtcAppType, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fguard(s, v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof_5fguard(s, v3, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_5_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.is_node(v4, Some(Constructor::eo__24emb_5fFunType)) { Ok(v) => v, Err(e) => return Err(e) };
if !v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eFunType, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof_5fguard(s, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24smtx_5ftypeof_5fguard(s, v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_10_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fguard(s, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_11_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Array, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eMap, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof_5fguard(s, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24smtx_5ftypeof_5fguard(s, v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_14_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5ftype_5ftuple(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24smtx_5ftype_5fwf(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_3_eo__24eo_5fto_5fsmt_5ftype(s, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_15_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSet, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fguard(s, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn cases_0_0_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_3_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, condition: Term, v2: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
Some(false) => {
let v5 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt_5ftype_5ftuple(s, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_5_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fString, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eVar, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v2: Term, v1: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eDtCons, &[v1, v6, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_6_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24eo_5fto_5fsmt(s, v4, v2, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn if_1_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v2: Term, v1: Term, v3: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v1, v7, v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_7_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtSel, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_1_eo__24eo_5fto_5fsmt(s, v5, v2, v1, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_1_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_8_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUConst, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::UconstId, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eUConst, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eBoolean, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eBoolean, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftype_5fwf(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eBoolean, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn case_1_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn case_2_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eRational, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn if_0_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_3_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eString, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_op(NativeOp::StringValid, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn cases_0_0_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_1_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.native_op(NativeOp::IntToNat, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_4_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eBinary, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Zleq, &[v3, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::IntPow2, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::ModTotal, &[v2, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zeq, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::And, &[v4, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_1_eo__24smtx_5ftypeof(s, v8, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v12)))
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fite(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a1)
}
Some(false) => {
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_op(NativeOp::Teq, &[a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24smtx_5ftypeof_5fite(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_ite"
pub fn eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fite(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_2_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5f_3d(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_op(NativeOp::Teq, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24smtx_5ftypeof_5f_3d(s, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fguard(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24smtx_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5f_3d(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_="
pub fn eo__24smtx_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5f_3d(s, a0, a1);
s.leave();
result
}
pub(super) fn case_12_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_40purify, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(Next::Again([v1])))
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_arith_overload_op_2"
pub fn eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
Ok(Some(a2))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
Ok(Some(a2))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_arith_overload_op_2_ret"
pub fn eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_11_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_12_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_13_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_arith_overload_op_1"
pub fn eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s, a0);
s.leave();
result
}
pub(super) fn if_14_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_20_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_22_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_24_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fselect(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fselect(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::Teq, &[v1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_0_eo__24smtx_5ftypeof_5fselect(s, v3, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fselect(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fselect(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fselect(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fselect(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_select"
pub fn eo__24smtx_5ftypeof_5fselect(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fselect(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fstore(s: &mut Store, condition: Term, v1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eMap, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24smtx_5ftypeof_5fstore(s: &mut Store, condition: Term, v2: Term, a2: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match s.native_op(NativeOp::Teq, &[v2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5ftypeof_5fstore(s, v4, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fstore(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::Teq, &[v1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_1_eo__24smtx_5ftypeof_5fstore(s, v3, v2, a2, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fstore(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fstore(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fstore(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fstore(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_store"
pub fn eo__24smtx_5ftypeof_5fstore(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fstore(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fmap_5fdiff(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v1)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fmap_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_op(NativeOp::Teq, &[v1, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Teq, &[v2, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::And, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24smtx_5ftypeof_5fmap_5fdiff(s, v8, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn if_1_eo__24smtx_5ftypeof_5fmap_5fdiff(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v1)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fmap_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_1_eo__24smtx_5ftypeof_5fmap_5fdiff(s, v4, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5fmap_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fmap_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fmap_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fmap_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5fmap_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_map_diff"
pub fn eo__24smtx_5ftypeof_5fmap_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fmap_5fdiff(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::NatToInt, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::NatToInt, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Zplus, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::IntToNat, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_concat"
pub fn eo__24smtx_5ftypeof_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fconcat(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fextract(s: &mut Store, condition: Term, v1: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.native_op(NativeOp::Zplus, &[v1, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.native_op(NativeOp::Zneg, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.native_op(NativeOp::Zplus, &[v17, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.native_op(NativeOp::IntToNat, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
Some(false) => {
let v22 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24smtx_5ftypeof_5fextract(s: &mut Store, condition: Term, v1: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.native_op(NativeOp::Zplus, &[v1, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Zneg, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.native_op(NativeOp::Zplus, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.native_op(NativeOp::Zlt, &[v10, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match if_0_eo__24smtx_5ftypeof_5fextract(s, v15, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24smtx_5ftypeof_5fextract(s: &mut Store, condition: Term, v5: Term, v1: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.native_op(NativeOp::NatToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::Zlt, &[v1, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_1_eo__24smtx_5ftypeof_5fextract(s, v9, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
Some(false) => {
let v26 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fextract(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zleq, &[v6, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_2_eo__24smtx_5ftypeof_5fextract(s, v7, v5, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fextract(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fextract(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fextract(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fextract(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_extract"
pub fn eo__24smtx_5ftypeof_5fextract(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fextract(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5frepeat(s: &mut Store, condition: Term, v3: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.native_op(NativeOp::NatToInt, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zmult, &[v1, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::IntToNat, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5frepeat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Zleq, &[v4, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_0_eo__24smtx_5ftypeof_5frepeat(s, v5, v3, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5frepeat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5frepeat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5frepeat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5frepeat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_repeat"
pub fn eo__24smtx_5ftypeof_5frepeat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5frepeat(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fbv_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_bv_op_1"
pub fn eo__24smtx_5ftypeof_5fbv_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fbv_5fop_5f1(s, a0);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Nateq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v4, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_bv_op_2"
pub fn eo__24smtx_5ftypeof_5fbv_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Nateq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_bv_op_2_ret"
pub fn eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fzero_5fextend(s: &mut Store, condition: Term, v3: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.native_op(NativeOp::NatToInt, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zplus, &[v1, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::IntToNat, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fzero_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Zleq, &[v4, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_0_eo__24smtx_5ftypeof_5fzero_5fextend(s, v5, v3, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fzero_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fzero_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fzero_5fextend(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fzero_5fextend(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_zero_extend"
pub fn eo__24smtx_5ftypeof_5fzero_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fzero_5fextend(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fsign_5fextend(s: &mut Store, condition: Term, v3: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.native_op(NativeOp::NatToInt, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zplus, &[v1, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::IntToNat, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fsign_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Zleq, &[v4, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_0_eo__24smtx_5ftypeof_5fsign_5fextend(s, v5, v3, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fsign_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fsign_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fsign_5fextend(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fsign_5fextend(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_sign_extend"
pub fn eo__24smtx_5ftypeof_5fsign_5fextend(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fsign_5fextend(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5frotate_5fleft(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5frotate_5fleft(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Zleq, &[v4, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24smtx_5ftypeof_5frotate_5fleft(s, v5, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5frotate_5fleft(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5frotate_5fleft(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5frotate_5fleft(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5frotate_5fleft(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_rotate_left"
pub fn eo__24smtx_5ftypeof_5frotate_5fleft(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5frotate_5fleft(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5frotate_5fright(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5frotate_5fright(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Zleq, &[v4, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24smtx_5ftypeof_5frotate_5fright(s, v5, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5frotate_5fright(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5frotate_5fright(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5frotate_5fright(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5frotate_5fright(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_rotate_right"
pub fn eo__24smtx_5ftypeof_5frotate_5fright(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5frotate_5fright(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(a1))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_bv_op_1_ret"
pub fn eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a1)
}
Some(false) => {
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match if_0_eo__24smtx_5ftypeof_5fguard_5fwf(s, v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fguard_5fwf(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_guard_wf"
pub fn eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fguard_5fwf(s, a0, a1);
s.leave();
result
}
pub(super) fn case_78_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eseq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(a1))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_seq_op_1_ret"
pub fn eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s, v4, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_seq_op_2"
pub fn eo__24smtx_5ftypeof_5fseq_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fseq_5fop_5f2(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fstr_2esubstr(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v2 { return Ok(None); }
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fstr_2esubstr(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fstr_2esubstr(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fstr_2esubstr(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fstr_2esubstr(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_str.substr"
pub fn eo__24smtx_5ftypeof_5fstr_2esubstr(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fstr_2esubstr(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s, v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_seq_op_2_ret"
pub fn eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s: &mut Store, condition: Term, v3: Term, v5: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.native_op(NativeOp::Teq, &[v3, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s, v7, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s, v6, v3, v5, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_seq_op_3"
pub fn eo__24smtx_5ftypeof_5fseq_5fop_5f3(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fseq_5fop_5f3(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fstr_2eindexof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fstr_2eindexof(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v4 { return Ok(None); }
let v5 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24smtx_5ftypeof_5fstr_2eindexof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fstr_2eindexof(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fstr_2eindexof(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fstr_2eindexof(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fstr_2eindexof(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_str.indexof"
pub fn eo__24smtx_5ftypeof_5fstr_2eindexof(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fstr_2eindexof(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fstr_2eat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v2 { return Ok(None); }
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fstr_2eat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fstr_2eat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fstr_2eat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fstr_2eat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_str.at"
pub fn eo__24smtx_5ftypeof_5fstr_2eat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fstr_2eat(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fseq_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_seq_op_1"
pub fn eo__24smtx_5ftypeof_5fseq_5fop_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fseq_5fop_5f1(s, a0);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fstr_2eupdate(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fstr_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v2 { return Ok(None); }
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.native_op(NativeOp::Teq, &[v1, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24smtx_5ftypeof_5fstr_2eupdate(s, v5, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fstr_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fstr_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fstr_2eupdate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fstr_2eupdate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_str.update"
pub fn eo__24smtx_5ftypeof_5fstr_2eupdate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fstr_2eupdate(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_26_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_27_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_28_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_29_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_30_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_31_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_32_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_33_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_35_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_37_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_40_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_43_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v14 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_103_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_104_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_105_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn if_46_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_47_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_48_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fre_2e_5e(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fre_2e_5e(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v2 { return Ok(None); }
let v3 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Zleq, &[v3, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5ftypeof_5fre_2e_5e(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fre_2e_5e(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fre_2e_5e(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fre_2e_5e(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fre_2e_5e(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_re.^"
pub fn eo__24smtx_5ftypeof_5fre_2e_5e(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fre_2e_5e(s, a0, a1);
s.leave();
result
}
pub(super) fn if_49_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_50_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_51_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_53_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_55_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_57_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_59_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fre_2eloop(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24smtx_5ftypeof_5fre_2eloop(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Zleq, &[v7, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_0_eo__24smtx_5ftypeof_5fre_2eloop(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fre_2eloop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v4 { return Ok(None); }
let v5 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Zleq, &[v5, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_1_eo__24smtx_5ftypeof_5fre_2eloop(s, v6, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fre_2eloop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fre_2eloop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fre_2eloop(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fre_2eloop(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_re.loop"
pub fn eo__24smtx_5ftypeof_5fre_2eloop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fre_2eloop(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_61_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fseq_2enth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v2 { return Ok(None); }
let v3 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v1, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fseq_2enth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fseq_2enth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fseq_2enth(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fseq_2enth(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_seq.nth"
pub fn eo__24smtx_5ftypeof_5fseq_2enth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fseq_2enth(s, a0, a1);
s.leave();
result
}
pub(super) fn if_63_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v14 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fseq_5fdiff(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fseq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5ftypeof_5fseq_5fdiff(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fseq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fseq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fseq_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fseq_5fdiff(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_seq_diff"
pub fn eo__24smtx_5ftypeof_5fseq_5fdiff(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fseq_5fdiff(s, a0, a1);
s.leave();
result
}
pub(super) fn if_66_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v14 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_69_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_126_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eset_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eSet, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eSet, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSet, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s, v4, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_sets_op_2"
pub fn eo__24smtx_5ftypeof_5fsets_5fop_5f2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fsets_5fop_5f2(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fset_2emember(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fset_2emember(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_op(NativeOp::Teq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_0_eo__24smtx_5ftypeof_5fset_2emember(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fset_2emember(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fset_2emember(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fset_2emember(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fset_2emember(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_set.member"
pub fn eo__24smtx_5ftypeof_5fset_2emember(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fset_2emember(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.native_op(NativeOp::Teq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s, v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_sets_op_2_ret"
pub fn eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_70_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_71_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.native_op(NativeOp::IntToNat, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v2 { return Ok(None); }
let v3 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Zleq, &[v3, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s, v4, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_int_to_bv"
pub fn eo__24smtx_5ftypeof_5fint_5fto_5fbv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fint_5fto_5fbv(s, a0, a1);
s.leave();
result
}
pub(super) fn case_1_eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dd_lookup"
pub fn eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(972), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdd_5flookup(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(972), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24smtx_5fdd_5flookup(s, v4, v2, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24smtx_5fdd_5flookup(s: &mut Store, condition: Term, v2: Term, a0: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v5 = match eo__24smtx_5fdd_5flookup(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dtc_resolve"
pub fn eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(982), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdtc_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(982), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dt_resolve"
pub fn eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(979), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(979), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdtc_5fresolve(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
Ok(Some(Next::Done(a0)))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
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
pub(super) fn case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
// EO program "$smtx_typeof_dt_cons_rec"
pub fn eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1000), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1000), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) {
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
pub(super) fn step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eDtcAppType, &[v4, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_141_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdd_5flookup(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5fdt_5fresolve(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, v5, v7, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v4, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
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
pub(super) fn case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v9, v10, v8])))
}
pub(super) fn case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
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
pub(super) fn case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) {
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
// EO program "$smtx_ret_typeof_sel_rec"
pub fn eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(985), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(985), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24smtx_5fret_5ftypeof_5fsel(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24smtx_5fdt_5fresolve(s, v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, v1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24smtx_5fret_5ftypeof_5fsel(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fret_5ftypeof_5fsel(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_ret_typeof_sel"
pub fn eo__24smtx_5fret_5ftypeof_5fsel(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5fret_5ftypeof_5fsel(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fapply(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eFunType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::Teq, &[v1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_0_eo__24smtx_5ftypeof_5fapply(s, v3, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fguard(s, v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_1_eo__24smtx_5ftypeof_5fapply(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::Teq, &[v1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_1_eo__24smtx_5ftypeof_5fapply(s, v3, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fguard(s, v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_apply"
pub fn eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fapply(s, a0, a1);
s.leave();
result
}
pub(super) fn case_145_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_146_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eUConst, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_147_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
// EO program "$smtx_typeof"
pub fn eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_type(TypeCacheKind::Smt, cache_args[0]) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftypeof(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_type(TypeCacheKind::Smt, cache_args[0], value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftypeof(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5ftypeof(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match cases_2_0_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_1_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_2_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_5_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eite, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fite(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_6_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2enot, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_2_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_7_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eor, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_4_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_8_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eand, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_6_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_9_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3d_3e, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_8_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_10_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2exor, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_10_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_11_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3d, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5f_3d(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_13_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_2b, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_14_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_2d, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_15_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_2a, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_16_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3c, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_17_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3c_3d, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_18_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3e, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_19_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3e_3d, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_20_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eto_5freal, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_11_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_21_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eto_5fint, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_12_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_22_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eis_5fint, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_13_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_23_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eabs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_24_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2euneg, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_25_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ediv, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_15_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_26_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2emod, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_17_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_27_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2edivisible, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_19_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_28_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eint_2epow2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_20_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_29_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eint_2elog2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_21_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_30_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ediv_5ftotal, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_23_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_31_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2emod_5ftotal, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_25_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_32_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eselect, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fselect(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_33_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estore, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fstore(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_34_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2emap_5fdiff, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fmap_5fdiff(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_35_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2econcat, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fconcat(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_36_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eextract, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fextract(s, v1, v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_37_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2erepeat, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5frepeat(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_38_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvnot, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftypeof_5fbv_5fop_5f1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_39_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvand, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_40_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvor, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_41_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvnand, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_42_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvnor, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_43_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvxor, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_44_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvxnor, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_45_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvcomp, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::NatSucc, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_46_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvneg, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftypeof_5fbv_5fop_5f1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_47_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvadd, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_48_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvmul, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_49_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvudiv, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_50_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvurem, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_51_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsub, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_52_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsdiv, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_53_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsrem, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_54_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsmod, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_55_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvult, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_56_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvule, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_57_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvugt, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_58_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvuge, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_59_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvslt, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_60_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsle, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_61_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsgt, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_62_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsge, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_63_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvshl, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_64_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvlshr, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_65_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvashr, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_66_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ezero_5fextend, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fzero_5fextend(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_67_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2esign_5fextend, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fsign_5fextend(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_68_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2erotate_5fleft, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5frotate_5fleft(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_69_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2erotate_5fright, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5frotate_5fright(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_70_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvuaddo, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_71_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvnego, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_72_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsaddo, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_73_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvumulo, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_74_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsmulo, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_75_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvusubo, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_76_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvssubo, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_77_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebvsdivo, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_79_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2elen, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_80_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2e_2b_2b, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fseq_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_81_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2esubstr, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fstr_2esubstr(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_82_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2econtains, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_83_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2ereplace, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fseq_5fop_5f3(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_84_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eindexof, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fstr_2eindexof(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_85_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eat, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fstr_2eat(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_86_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eprefixof, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_87_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2esuffixof, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_88_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2erev, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftypeof_5fseq_5fop_5f1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_89_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eupdate, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fstr_2eupdate(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_90_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eto_5flower, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_26_eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn case_91_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eto_5fupper, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_27_eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn case_92_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eto_5fcode, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_28_eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_93_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2efrom_5fcode, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_29_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_94_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eis_5fdigit, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_30_eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_95_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eto_5fint, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_31_eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_96_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2efrom_5fint, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_32_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_97_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2e_3c, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v3, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_34_eo__24smtx_5ftypeof(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v15)))
}
pub(super) fn case_98_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2e_3c_3d, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v3, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_36_eo__24smtx_5ftypeof(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v15)))
}
pub(super) fn case_99_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fall, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fseq_5fop_5f3(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_100_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fre, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Teq, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_39_eo__24smtx_5ftypeof(s, v7, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v22)))
}
pub(super) fn case_101_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fre_5fall, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Teq, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_42_eo__24smtx_5ftypeof(s, v7, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v22)))
}
pub(super) fn case_102_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eindexof_5fre, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Teq, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_45_eo__24smtx_5ftypeof(s, v7, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v20)))
}
pub(super) fn case_106_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eto_5fre, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_46_eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_107_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2e_2a, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_47_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_108_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2e_2b, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_48_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_109_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2e_5e, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fre_2e_5e(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_110_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2eopt, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_49_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_111_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2ecomp, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_50_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_112_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2erange, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v3, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_52_eo__24smtx_5ftypeof(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v15)))
}
pub(super) fn case_113_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2e_2b_2b, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_54_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_114_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2einter, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_56_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_115_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2eunion, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_58_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_116_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2ediff, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_60_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn case_117_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2eloop, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fre_2eloop(s, v1, v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_118_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2ein_5fre, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v3, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_62_eo__24smtx_5ftypeof(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v14)))
}
pub(super) fn case_119_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eseq_2eunit, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_120_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eseq_2enth, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fseq_2enth(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_121_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Teq, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_65_eo__24smtx_5ftypeof(s, v7, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v20)))
}
pub(super) fn case_122_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eseq_5fdiff, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fseq_5fdiff(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_123_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_40strings_5foccur_5findex, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fstr_2eindexof(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_124_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Teq, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_68_eo__24smtx_5ftypeof(s, v7, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v20)))
}
pub(super) fn case_125_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2echoice, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_69_eo__24smtx_5ftypeof(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn case_127_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eset_2esingleton, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eSet, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eSet, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_128_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eset_2eunion, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fsets_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_129_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eset_2einter, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fsets_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_130_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eset_2eminus, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fsets_5fop_5f2(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_131_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eset_2emember, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fset_2emember(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_132_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eset_2esubset, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_133_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_2f, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_134_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_2f_5ftotal, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret(s, v3, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_135_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eforall, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_70_eo__24smtx_5ftypeof(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_136_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eexists, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_71_eo__24smtx_5ftypeof(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_137_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ebind, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_72_eo__24smtx_5ftypeof(s, v6, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_138_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eint_5fto_5fbv, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fint_5fto_5fbv(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_139_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eubv_5fto_5fint, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_140_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2esbv_5fto_5fint, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_142_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eApply, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtSel, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = fields[3];
let v8 = match eo__24smtx_5fret_5ftypeof_5fsel(s, v4, v5, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24smtx_5fret_5ftypeof_5fsel(s, v4, v5, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eFunType, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24smtx_5ftypeof_5fapply(s, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v14)))
}
pub(super) fn case_143_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eApply, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtTester, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5fdd_5flookup(s, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5fdt_5fresolve(s, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, v7, v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5ftsm_2eFunType, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24smtx_5ftypeof_5fapply(s, v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24smtx_5ftypeof_5fguard(s, v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v16)))
}
pub(super) fn case_144_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eApply, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fapply(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn cases_0_1_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_4_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_8_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_3_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_12_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_4_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_16_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_5_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_20_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_21_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_22_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_23_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_6_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_24_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_25_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_26_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_27_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_7_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_28_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_29_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_30_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_31_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_8_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_32_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_33_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_34_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_35_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_9_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_36_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_37_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_38_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_39_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_10_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_40_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_41_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_42_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_43_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_11_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_44_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_45_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_46_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_47_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_12_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_48_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_49_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_50_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_51_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_13_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_52_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_53_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_54_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_55_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_14_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_56_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_57_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_58_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_59_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_15_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_60_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_61_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_62_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_63_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_16_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_64_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_65_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_66_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_67_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_17_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_68_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_69_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_70_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_71_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_18_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_72_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_73_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_74_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_75_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_19_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_76_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_77_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_78_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_79_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_20_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_80_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_81_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_82_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_83_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_21_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_84_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_85_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_86_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_87_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_22_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_88_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_89_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_90_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_91_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_23_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_92_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_93_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_94_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_95_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_24_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_96_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_97_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_98_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_99_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_25_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_100_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_101_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_102_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_103_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_26_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_104_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_105_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_106_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_107_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_27_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_108_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_109_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_110_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_111_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_28_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_112_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_113_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_114_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_115_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_29_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_116_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_117_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_118_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_119_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_30_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_120_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_121_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_122_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_123_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_31_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_124_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_125_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_126_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_127_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_32_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_128_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_129_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_130_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_131_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_33_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_132_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_133_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_134_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_135_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_34_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_136_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_137_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_138_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_139_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_35_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_140_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_141_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_142_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_143_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_36_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_144_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_145_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_146_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_147_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_0_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_4_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_6_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_7_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_2_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_8_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_9_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_10_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_11_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_3_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_12_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_13_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_14_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_15_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_4_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_16_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_17_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_18_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_19_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_5_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_20_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_21_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_22_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_23_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_6_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_24_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_25_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_26_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_27_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_7_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_28_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_29_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_30_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_31_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_8_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_32_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_33_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_34_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_35_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_9_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_0_36_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_0_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_1_0_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_1_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_2_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_3_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_1_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_1_4_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_5_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_6_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_7_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_2_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match cases_1_8_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_9_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_4_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_3_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_5_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_7_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_9_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_14_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_16_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_18_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_23_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_22_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_25_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_24_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_34_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_33_eo__24smtx_5ftypeof(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_36_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_35_eo__24smtx_5ftypeof(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_38_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.native_op(NativeOp::Teq, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_37_eo__24smtx_5ftypeof(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_39_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_38_eo__24smtx_5ftypeof(s, v10, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_41_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.native_op(NativeOp::Teq, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_40_eo__24smtx_5ftypeof(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_42_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_41_eo__24smtx_5ftypeof(s, v10, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_44_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Teq, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_43_eo__24smtx_5ftypeof(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_45_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_44_eo__24smtx_5ftypeof(s, v10, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_52_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_51_eo__24smtx_5ftypeof(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_54_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_53_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_56_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_55_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_58_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_57_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_60_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_59_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_62_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::Teq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_61_eo__24smtx_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_64_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Teq, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_63_eo__24smtx_5ftypeof(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_65_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_64_eo__24smtx_5ftypeof(s, v10, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_67_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Teq, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_66_eo__24smtx_5ftypeof(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_68_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_67_eo__24smtx_5ftypeof(s, v10, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_72_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v4: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn more_3_eo__24eo_5fto_5fsmt(s: &mut Store, v7: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2eand, &[v7, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2emap_5fdiff, &[a0, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_array_deq_diff"
pub fn eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fbv_5fsize(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eBitVec, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_op(NativeOp::NatToInt, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fbv_5fsize(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.native_op(NativeOp::Zneg, &[v0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fbv_5fsize(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fbv_5fsize(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fbv_5fsize(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_bv_size"
pub fn eo__24eo_5fto_5fsmt_5fbv_5fsize(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fbv_5fsize(s, a0);
s.leave();
result
}
pub(super) fn more_5_eo__24eo_5fto_5fsmt(s: &mut Store, v14: Term, v15: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v14, v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn more_6_eo__24eo_5fto_5fsmt(s: &mut Store, v13: Term, v14: Term, v9: Term, v12: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v9, v12, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn more_7_eo__24eo_5fto_5fsmt(s: &mut Store, v13: Term, v14: Term, v9: Term, v12: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v9, v12, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn more_8_eo__24eo_5fto_5fsmt(s: &mut Store, v8: Term, v11: Term, v14: Term, v7: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v8, v11, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5fsm_2econcat, &[v7, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fseq_2eempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eseq_2eempty, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fseq_2eempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fseq_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fseq_2eempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fseq_2eempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_seq.empty"
pub fn eo__24eo_5fto_5fsmt_5fseq_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fseq_2eempty(s, a0);
s.leave();
result
}
pub(super) fn case_94_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fto_5fsmt_5fseq_2eempty(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_119_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_120_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_121_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fnat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_op(NativeOp::IntToNat, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fnat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fnat(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fnat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fnat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_nat"
pub fn eo__24eo_5fto_5fsmt_5fnat(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fnat(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2e_2b_2b, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit, &[a0, v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[a0, v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2ere_2e_2b_2b, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit, &[a0, v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit, &[a0, v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2e_2d, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[a0, v5, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v9, v2, v4])))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s, a0, a1, a2) {
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
// EO program "$eo_to_smt_re_unfold_pos_component"
pub fn eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(749), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(749), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.native_op(NativeOp::Zleq, &[v2, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_nat_is_valid"
pub fn eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, a0);
s.leave();
result
}
pub(super) fn more_11_eo__24eo_5fto_5fsmt(s: &mut Store, v4: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eindexof_5fre, &[v4, v12, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_14_eo__24eo_5fto_5fsmt(s: &mut Store, v16: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo__24emb_5fsm_2e_2d, &[v16, v26]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_16_eo__24eo_5fto_5fsmt(s: &mut Store, v16: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo__24emb_5fsm_2e_2d, &[v16, v26]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftester(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.construct(Constructor::eo__24emb_5fsm_2eDtTester, &[v1, v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftester(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftester(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftester(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftester(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_tester"
pub fn eo__24eo_5fto_5fsmt_5ftester(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5ftester(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fupdater_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtSel, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
Ok(Some(a4))
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5fupdater_5frec(s: &mut Store, condition: Term, a3: Term, v1: Term, v2: Term, v3: Term, v6: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a3)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v1, v2, v3, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v10, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5fupdater_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_to_smt_updater_rec"
pub fn eo__24eo_5fto_5fsmt_5fupdater_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(766), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fupdater_5frec(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(766), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fupdater_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fupdater_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fupdater_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5fupdater_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fupdater_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtSel, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match s.native_pattern_succ(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v1, v2, v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5fupdater_5frec(s, v7, v6, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::Nateq, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_0_eo__24eo_5fto_5fsmt_5fupdater_5frec(s, v9, a3, v1, v2, v3, v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v8, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_1_eo__24smtx_5fdtc_5fnum_5fsels(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dtc_num_sels"
pub fn eo__24smtx_5fdtc_5fnum_5fsels(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(981), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdtc_5fnum_5fsels(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(981), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdtc_5fnum_5fsels(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdtc_5fnum_5fsels(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdtc_5fnum_5fsels(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdtc_5fnum_5fsels(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdtc_5fnum_5fsels(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::NatSucc, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_0_eo__24smtx_5fdt_5fnum_5fsels(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = match eo__24smtx_5fdtc_5fnum_5fsels(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fnum_5fsels(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([v2, v4])))
}
pub(super) fn case_2_eo__24smtx_5fdt_5fnum_5fsels(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn step_eo__24smtx_5fdt_5fnum_5fsels(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24smtx_5fdt_5fnum_5fsels(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fnum_5fsels(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fdt_5fnum_5fsels(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24smtx_5fdt_5fnum_5fsels(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5fdt_5fnum_5fsels(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$smtx_dt_num_sels"
pub fn eo__24smtx_5fdt_5fnum_5fsels(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(978), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fnum_5fsels(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(978), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5fupdater(s: &mut Store, condition: Term, v1: Term, v2: Term, v3: Term, a1: Term, v4: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2eDtTester, &[v1, v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v10, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v1, v2, v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24smtx_5fdd_5flookup(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24smtx_5fdt_5fnum_5fsels(s, v13, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2eDtCons, &[v1, v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fto_5fsmt_5fupdater_5frec(s, v12, v14, a1, a2, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v11, v16, a1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
Some(false) => {
let v18 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fupdater(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtSel, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match s.native_op(NativeOp::NatToInt, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdd_5flookup(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5fdt_5fnum_5fsels(s, v6, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::NatToInt, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::Zlt, &[v5, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_0_eo__24eo_5fto_5fsmt_5fupdater(s, v9, v1, v2, v3, a1, v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fupdater(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fupdater(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fupdater(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fupdater(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_updater"
pub fn eo__24eo_5fto_5fsmt_5fupdater(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fupdater(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_151_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fdd_2econs, &[v2, v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eDtCons, &[v1, v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_pattern_nat_zero(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
Ok(Some(a4))
}
// EO program "$eo_to_smt_tuple_prepend_rec"
pub fn eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(759), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(759), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_pattern_succ(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s, a0, a1, a2, v1, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v3, a0, v4, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v5, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn more_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s: &mut Store, v35: Term, v36: Term, v34: Term, a1: Term, v27: Term, v29: Term, a3: Term, v33: Term) -> CheckResult<Term> {
let v37 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v35, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__24emb_5fsm_2eDtCons, &[v34, v38, v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v40, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec(s, v27, v29, a3, v33, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
pub(super) fn if_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s: &mut Store, condition: Term, v8: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v25 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v8, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v8, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v8, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24smtx_5fdt_5fnum_5fsels(s, v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[a2, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s, v35, v36, v34, a1, v27, v29, a3, v33)
}
Some(false) => {
let v43 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s: &mut Store, a2: Term, v8: Term, v16: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
let v17 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[a2, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v17, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24smtx_5ftype_5fwf(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.native_op(NativeOp::And, &[v16, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s, v24, v8, a2, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v44))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = fields[1];
let v10 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v11 { return Ok(None); }
let v12 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Streq, &[v1, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.native_op(NativeOp::Streq, &[v4, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.native_op(NativeOp::And, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s, a2, v8, v16, a1, a3)
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_tuple_prepend_of_type"
pub fn eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5ftypeof(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5fof_5ftype(s, v0, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_tuple_prepend"
pub fn eo__24eo_5fto_5fsmt_5ftuple_5fprepend(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s: &mut Store, condition: Term, v5: Term, v9: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.native_op(NativeOp::IntToNat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v18, v19, v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v22, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s: &mut Store, v14: Term, v16: Term, v5: Term, v9: Term, a2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.native_op(NativeOp::And, &[v14, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s, v17, v5, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v7 { return Ok(None); }
let v8 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.native_op(NativeOp::Streq, &[v1, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Streq, &[v4, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.native_op(NativeOp::And, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.native_op(NativeOp::Zleq, &[v15, v9]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s, v14, v16, v5, v9, a2)
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_tuple_select"
pub fn eo__24eo_5fto_5fsmt_5ftuple_5fselect(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5ftuple_5fselect(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s: &mut Store, condition: Term, v5: Term, v9: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24eo_5fto_5fsmt_5ftuple_5fdecl(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.native_op(NativeOp::IntToNat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v18, v19, v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fto_5fsmt_5fupdater(s, v22, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s: &mut Store, v14: Term, v16: Term, v5: Term, v9: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v17 = match s.native_op(NativeOp::And, &[v14, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_0_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s, v17, v5, v9, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v7 { return Ok(None); }
let v8 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.native_op(NativeOp::Streq, &[v1, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,84,117,112,108,101,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.native_op(NativeOp::Streq, &[v4, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.native_op(NativeOp::And, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.native_op(NativeOp::Zleq, &[v15, v9]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s, v14, v16, v5, v9, a2, a3)
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_tuple_update"
pub fn eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fset_2eempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2eempty, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fset_2eempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fset_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fset_2eempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fset_2eempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_set.empty"
pub fn eo__24eo_5fto_5fsmt_5fset_2eempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fset_2eempty(s, a0);
s.leave();
result
}
pub(super) fn case_155_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_set_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fto_5fsmt_5fset_2eempty(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_set_elem_type"
pub fn eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.construct(Constructor::eo__24emb_5fsm_2emap_5fdiff, &[a0, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_sets_deq_diff"
pub fn eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_170_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fexists(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5fexists(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_to_smt_exists"
pub fn eo__24eo_5fto_5fsmt_5fexists(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(745), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fexists(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(745), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fexists(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fexists(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fexists(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5fexists(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fexists(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.destruct(Constructor::eo__24emb_5fString, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match eo__24eo_5fto_5fsmt_5ftype(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt_5fexists(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2eexists, &[v11, v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_172_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v10 = match s.destruct(Constructor::eo__24emb_5fString, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v12 else { return Ok(None); }
;
let v13 = match eo__24eo_5fto_5fsmt_5ftype(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fto_5fsmt_5fexists(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2echoice, &[v11, v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v15)))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v10 = match s.destruct(Constructor::eo__24emb_5fString, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v12 else { return Ok(None); }
;
let v13 = fields[0];
let v14 = match eo__24eo_5fto_5fsmt_5ftype(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5fto_5fsmt_5ftype(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fto_5fsmt_5fexists(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2echoice, &[v11, v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24emb_5fsm_2ebind, &[v11, v14, v17, a1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v18, v13])))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s, a0, a1, a2) {
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
// EO program "$eo_to_smt_quantifiers_skolemize"
pub fn eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(748), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(748), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn if_22_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match eo__24eo_5fto_5fsmt_5fnat(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::ConstId, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eUConst, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_178_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40const, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_22_eo__24eo_5fto_5fsmt(s, v3, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_180_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_45_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_180_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
