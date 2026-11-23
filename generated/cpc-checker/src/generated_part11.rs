//! Generated functions, module 11 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
// EO program "$run_evaluate"
pub fn eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(973), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24run_5fevaluate(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(973), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_2_0_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_1_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::IsQ, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsQ, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::And, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match if_4_eo__24run_5fevaluate(s, v11, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v56))
}
pub(super) fn case_1_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Not, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_2_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_5_eo__24run_5fevaluate(s, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_3_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Or, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_4_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Not, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Or, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_5_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::And, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_6_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Xor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_7_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Neg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_8_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Neg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Neg, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24run_5fevaluate(s, v12, v14, v11)
}
pub(super) fn case_9_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Neg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_10_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Neg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Neg, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24run_5fevaluate(s, v12, v14, v11)
}
pub(super) fn case_11_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_12_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Neg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_13_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Mul, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_14_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Neg, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_15_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToRat, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToRat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::RatDiv, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_16_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToRat, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v10 = match s.literal(Lit::Rational(v9)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Eq, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_8_eo__24run_5fevaluate(s, v11, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_17_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IntDiv, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_18_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_9_eo__24run_5fevaluate(s, v9, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_19_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IntMod, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_20_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_10_eo__24run_5fevaluate(s, v9, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_21_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToRat, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_22_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToInt, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_23_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_is_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToInt, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::ToRat, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToRat, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v6, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_24_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsNeg, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_11_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_25_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsZ, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_13_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_26_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsZ, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_15_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_27_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsZ, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match if_19_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn case_28_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Concat, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_29_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Length, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_30_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Add, &[v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24run_5fevaluate(s, v10, v11, v16)
}
pub(super) fn case_31_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Extract, &[v7, v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_32_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Find, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Not, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_33_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::ToString, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::ToString, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Find, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_23_eo__24run_5fevaluate(s, v15, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_35_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Length, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Extract, &[v8, v9, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24run_5fevaluate(s, v7, v14)
}
pub(super) fn case_36_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2esuffixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Length, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Length, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Neg, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[v10, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24run_5fevaluate(s, v2, v8, v14, v7)
}
pub(super) fn case_37_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match if_30_eo__24run_5fevaluate(s, v11, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v46))
}
pub(super) fn case_38_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Length, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Eq, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_32_eo__24run_5fevaluate(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_39_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsZ, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_37_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_40_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsStr, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match if_39_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_41_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsZ, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match if_42_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn case_42_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::IsStr, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsStr, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::And, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_43_eo__24run_5fevaluate(s, v11, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_43_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsStr, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_44_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_44_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsStr, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_45_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_45_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsStr, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_46_eo__24run_5fevaluate(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_46_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Gt, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Length, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Gt, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_50_eo__24run_5fevaluate(s, v12, v16, v8, v5, v2)
}
pub(super) fn case_47_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Not, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_48_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Neg, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_49_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_50_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Mul, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_51_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Eq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match if_53_eo__24run_5fevaluate(s, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v36))
}
pub(super) fn case_52_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Eq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_54_eo__24run_5fevaluate(s, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_53_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::And, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_54_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Or, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_55_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Xor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_56_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Concat, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_57_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Neg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_58_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_extract, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Extract, &[v6, v5, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_59_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Gt, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_60_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Gt, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Or, &[v9, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_61_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvugt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Gt, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_62_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvuge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Gt, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Or, &[v9, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_63_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_63_eo__24run_5fevaluate(s, v14, v7, v12, v2, v5)
}
pub(super) fn case_64_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_81_eo__24run_5fevaluate(s, v14, v7, v12, v2, v5)
}
pub(super) fn case_65_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_94_eo__24run_5fevaluate(s, v14, v7, v12, v5, v2)
}
pub(super) fn case_66_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_112_eo__24run_5fevaluate(s, v14, v7, v12, v5, v2)
}
pub(super) fn case_67_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Gt, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match if_119_eo__24run_5fevaluate(s, v11, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn case_68_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Gt, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match if_122_eo__24run_5fevaluate(s, v11, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn case_69_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitwidth(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fbitwidth(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_129_eo__24run_5fevaluate(s, v5, v9, v14, v2, v8)
}
pub(super) fn case_70_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_repeat, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24run_5fevaluate(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::IsZ, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24run_5fevaluate(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::IsNeg, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Not, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::And, &[v6, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_131_eo__24run_5fevaluate(s, v10, v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_71_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_sign_5fextend, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24bv_5fbitwidth(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_136_eo__24run_5fevaluate(s, v13, v14, v2, v10, v9)
}
pub(super) fn case_72_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_zero_5fextend, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24bv_5fbitwidth(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24run_5fevaluate(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::ToInt, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::ToBin, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_74_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_int_5fto_5fbv, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24run_5fevaluate(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::ToBin, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_75_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToInt, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_76_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_sbv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24bv_5fbitwidth(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match if_140_eo__24run_5fevaluate(s, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v49))
}
pub(super) fn cases_0_0_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_3_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_4_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_5_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_20_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_21_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_22_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_23_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_6_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_24_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_25_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_26_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_27_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_7_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_28_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_29_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_30_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_31_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_8_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_32_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_33_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_34_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_35_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_9_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_36_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_37_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_38_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_39_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_10_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_40_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_41_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_42_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_43_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_11_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_44_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_45_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_46_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_47_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_12_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_48_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_49_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_50_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_51_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_13_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_52_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_53_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_54_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_55_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_14_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_56_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_57_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_58_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_59_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_15_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_60_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_61_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_62_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_63_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_16_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_64_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_65_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_66_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_67_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_17_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_68_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_69_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_70_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_71_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_18_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_72_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_73_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_74_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_75_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_19_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_76_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_77_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_6_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_7_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_2_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_8_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_9_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_10_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_11_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_3_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_12_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_13_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_14_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_15_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_4_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_16_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_17_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_18_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_19_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_0_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_0_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_1_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_2_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_3_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_1_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_4_eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v44 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_core(EvalOp::Eq, &[v44, v45]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v46)
}
Some(false) => {
let v47 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v51)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v36 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_core(EvalOp::Eq, &[v36, v37]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
Some(false) => {
let v39 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::IsBool, &[v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_core(EvalOp::IsBool, &[v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_core(EvalOp::And, &[v40, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match if_0_eo__24run_5fevaluate(s, v43, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v52)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v28 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Eq, &[v28, v29]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
Some(false) => {
let v31 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::IsStr, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::IsStr, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_core(EvalOp::And, &[v32, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match if_1_eo__24run_5fevaluate(s, v35, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v53)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v20 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Eq, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
Some(false) => {
let v23 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::IsBin, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::IsBin, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::And, &[v24, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match if_2_eo__24run_5fevaluate(s, v27, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v54)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::IsZ, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsZ, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::And, &[v16, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match if_3_eo__24run_5fevaluate(s, v19, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v55)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v13 = match s.literal(Lit::Rational(v12)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::ToRat, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::ToRat, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::RatDiv, &[v15, v17]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::IntDiv, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::IntMod, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Neg, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_12_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Log, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_13_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_12_eo__24run_5fevaluate(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Pow, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_14_eo__24run_5fevaluate(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Log, &[v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IsNeg, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_16_eo__24run_5fevaluate(s, v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::IsZ, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match if_17_eo__24run_5fevaluate(s, v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::Pow, &[v10, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Eq, &[v9, v24]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_18_eo__24run_5fevaluate(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
Some(false) => {
let v27 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_21_eo__24run_5fevaluate(s: &mut Store, v8: Term, v5: Term, v28: Term) -> CheckResult<Term> {
let v29 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::ToString, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::ToString, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::Find, &[v31, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_core(EvalOp::Length, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::Add, &[v34, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Length, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Extract, &[v29, v37, v39]) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24run_5fevaluate(s, v28, v40)
}
pub(super) fn if_23_eo__24run_5fevaluate(s: &mut Store, condition: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::ToString, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::ToString, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Find, &[v20, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Add, &[v23, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::Extract, &[v17, v18, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Concat, &[v26, v27]) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24run_5fevaluate(s, v8, v5, v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_27_eo__24run_5fevaluate(s: &mut Store, v2: Term, v8: Term, v14: Term, v7: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Length, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Add, &[v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Extract, &[v8, v14, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Eq, &[v7, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn if_28_eo__24run_5fevaluate(s: &mut Store, condition: Term, v8: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::Length, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Extract, &[v27, v2, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::ToString, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::ToString, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::Find, &[v31, v33]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v34)
}
Some(false) => {
let v35 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::Length, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_core(EvalOp::Extract, &[v35, v2, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::ToString, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_core(EvalOp::ToString, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_core(EvalOp::Find, &[v39, v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_core(EvalOp::Add, &[v2, v42]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_29_eo__24run_5fevaluate(s: &mut Store, condition: Term, v8: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v17 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
Some(false) => {
let v18 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Length, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Extract, &[v18, v2, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::ToString, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::ToString, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Find, &[v22, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::IsNeg, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_28_eo__24run_5fevaluate(s, v26, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_30_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Length, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Gt, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match if_29_eo__24run_5fevaluate(s, v16, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_31_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_32_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::ToInt, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Length, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::IsZ, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_31_eo__24run_5fevaluate(s, v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_33_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(196608u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Gt, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_34_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::IsNeg, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Not, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_35_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Numeral(Integer::from(196608u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Eq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_33_eo__24run_5fevaluate(s, v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_34_eo__24run_5fevaluate(s, v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_37_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::IsZ, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_35_eo__24run_5fevaluate(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_36_eo__24run_5fevaluate(s, v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
Some(false) => {
let v26 = match s.construct(Constructor::eo_str_2efrom_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_38_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24str_5fflatten(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListRev, &[v10, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24str_5fto_5fint_5feval_5frec(s, v15, v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_39_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_38_eo__24run_5fevaluate(s, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_40_eo__24run_5fevaluate(s: &mut Store, v14: Term, v15: Term, v2: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Log, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Add, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListRepeat, &[v16, v17, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24iota_5frec(s, v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn if_41_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Log, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IsNeg, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match requires_40_eo__24run_5fevaluate(s, v14, v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24str_5ffrom_5fint_5feval_5frec(s, v26, v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_42_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match if_41_eo__24run_5fevaluate(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
Some(false) => {
let v31 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_43_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24str_5fflatten(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5fflatten(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24str_5fleq_5feval_5frec(s, v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_44_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24str_5fflatten(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5fcase_5fconv_5frec(s, v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_45_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24str_5fflatten(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5fcase_5fconv_5frec(s, v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_46_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5fflatten(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListRev, &[v7, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24str_5fcollect(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSingletonElim, &[v6, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_47_eo__24run_5fevaluate(s: &mut Store, v28: Term, v30: Term, v25: Term, v26: Term, v24: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let v31 = match s.builtin_core(EvalOp::Add, &[v28, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::Add, &[v31, v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::Extract, &[v25, v26, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_core(EvalOp::Concat, &[v24, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Length, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Add, &[v37, v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_core(EvalOp::Length, &[v41]) { Ok(v) => v, Err(e) => return Err(e) };
more_48_eo__24run_5fevaluate(s, v36, v40, v42, v35)
}
pub(super) fn if_49_eo__24run_5fevaluate(s: &mut Store, condition: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Add, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::Extract, &[v19, v20, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Neg, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24run_5fevaluate(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Length, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
more_47_eo__24run_5fevaluate(s, v28, v30, v25, v26, v24, v8, v5, v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_50_eo__24run_5fevaluate(s: &mut Store, v12: Term, v16: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.builtin_core(EvalOp::Or, &[v12, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match if_49_eo__24run_5fevaluate(s, v17, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v45))
}
pub(super) fn if_53_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fbitwidth(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24bv_5fbitwidth(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsZ, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match if_52_eo__24run_5fevaluate(s, v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::Add, &[v29, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::ToBin, &[v12, v31]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_core(EvalOp::IntDiv, &[v33, v34]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v35)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_54_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IntMod, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_55_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5ftypeof(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24bv_5fbitwidth(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Add, &[v37, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Pow, &[v34, v39]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_56_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5ftypeof(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24bv_5fbitwidth(s, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::Add, &[v29, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::IsNeg, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match if_55_eo__24run_5fevaluate(s, v32, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
Some(false) => {
let v42 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5ftypeof(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match eo__24bv_5fbitwidth(s, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Add, &[v45, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v42, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v48)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_58_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v21 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24bv_5fbitwidth(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Add, &[v23, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::IsZ, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match if_56_eo__24run_5fevaluate(s, v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::Neg, &[v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5ftypeof(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_57_eo__24run_5fevaluate(s, v54, v51, v52, v50)
}
Some(false) => {
let v61 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24eo_5ftypeof(s, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24bv_5fbitwidth(s, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_core(EvalOp::Add, &[v65, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_core(EvalOp::Extract, &[v61, v62, v67]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::ToInt, &[v68]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v69)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_59_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v97 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v97)
}
Some(false) => {
let v98 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match eo__24eo_5ftypeof(s, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match eo__24bv_5fbitwidth(s, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.builtin_core(EvalOp::Add, &[v101, v102]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.builtin_core(EvalOp::Pow, &[v98, v103]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v104)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_60_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v91 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24eo_5ftypeof(s, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24bv_5fbitwidth(s, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.builtin_core(EvalOp::Add, &[v93, v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.builtin_core(EvalOp::IsNeg, &[v95]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match if_59_eo__24run_5fevaluate(s, v96, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v105)
}
Some(false) => {
let v106 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match eo__24eo_5ftypeof(s, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match eo__24bv_5fbitwidth(s, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.builtin_core(EvalOp::Add, &[v109, v110]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v106, v111) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v112)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_62_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v85 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24eo_5ftypeof(s, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24bv_5fbitwidth(s, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_core(EvalOp::Add, &[v87, v88]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_core(EvalOp::IsZ, &[v89]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match if_60_eo__24run_5fevaluate(s, v90, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.builtin_core(EvalOp::Neg, &[v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match eo__24eo_5ftypeof(s, v117) { Ok(v) => v, Err(e) => return Err(e) };
more_61_eo__24run_5fevaluate(s, v118, v115, v116, v114)
}
Some(false) => {
let v125 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match eo__24eo_5ftypeof(s, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24bv_5fbitwidth(s, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_core(EvalOp::Add, &[v129, v130]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_core(EvalOp::Extract, &[v125, v126, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_core(EvalOp::ToInt, &[v132]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v133)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_64_eo__24run_5fevaluate(s: &mut Store, v74: Term, v75: Term, v5: Term, v71: Term, v70: Term) -> CheckResult<Option<Term>> {
let v76 = match s.builtin_core(EvalOp::Add, &[v74, v75]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match eo__24eo_5ftypeof(s, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match eo__24bv_5fbitwidth(s, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_core(EvalOp::Add, &[v79, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::Extract, &[v71, v76, v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_core(EvalOp::Eq, &[v82, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match if_62_eo__24run_5fevaluate(s, v84, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_core(EvalOp::Gt, &[v70, v134]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v135))
}
pub(super) fn more_63_eo__24run_5fevaluate(s: &mut Store, v14: Term, v7: Term, v12: Term, v2: Term, v5: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Add, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Extract, &[v7, v12, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Eq, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match if_58_eo__24run_5fevaluate(s, v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24bv_5fbitwidth(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_64_eo__24run_5fevaluate(s, v74, v75, v5, v71, v70)
}
pub(super) fn if_65_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5ftypeof(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24bv_5fbitwidth(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Add, &[v37, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Pow, &[v34, v39]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_66_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5ftypeof(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24bv_5fbitwidth(s, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::Add, &[v29, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::IsNeg, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match if_65_eo__24run_5fevaluate(s, v32, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
Some(false) => {
let v42 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5ftypeof(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match eo__24bv_5fbitwidth(s, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Add, &[v45, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v42, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v48)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_68_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v21 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24bv_5fbitwidth(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Add, &[v23, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::IsZ, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match if_66_eo__24run_5fevaluate(s, v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::Neg, &[v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5ftypeof(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_67_eo__24run_5fevaluate(s, v54, v51, v52, v50)
}
Some(false) => {
let v61 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24eo_5ftypeof(s, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24bv_5fbitwidth(s, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_core(EvalOp::Add, &[v65, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_core(EvalOp::Extract, &[v61, v62, v67]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::ToInt, &[v68]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v69)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_69_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v97 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v97)
}
Some(false) => {
let v98 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match eo__24eo_5ftypeof(s, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match eo__24bv_5fbitwidth(s, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.builtin_core(EvalOp::Add, &[v101, v102]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.builtin_core(EvalOp::Pow, &[v98, v103]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v104)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_70_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v91 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24eo_5ftypeof(s, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24bv_5fbitwidth(s, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.builtin_core(EvalOp::Add, &[v93, v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.builtin_core(EvalOp::IsNeg, &[v95]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match if_69_eo__24run_5fevaluate(s, v96, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v105)
}
Some(false) => {
let v106 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match eo__24eo_5ftypeof(s, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match eo__24bv_5fbitwidth(s, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.builtin_core(EvalOp::Add, &[v109, v110]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v106, v111) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v112)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_72_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v85 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24eo_5ftypeof(s, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24bv_5fbitwidth(s, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_core(EvalOp::Add, &[v87, v88]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_core(EvalOp::IsZ, &[v89]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match if_70_eo__24run_5fevaluate(s, v90, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.builtin_core(EvalOp::Neg, &[v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match eo__24eo_5ftypeof(s, v117) { Ok(v) => v, Err(e) => return Err(e) };
more_71_eo__24run_5fevaluate(s, v118, v115, v116, v114)
}
Some(false) => {
let v125 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match eo__24eo_5ftypeof(s, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24bv_5fbitwidth(s, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_core(EvalOp::Add, &[v129, v130]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_core(EvalOp::Extract, &[v125, v126, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_core(EvalOp::ToInt, &[v132]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v133)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_73_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v162 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v162)
}
Some(false) => {
let v163 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match eo__24eo_5ftypeof(s, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match eo__24bv_5fbitwidth(s, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.builtin_core(EvalOp::Add, &[v166, v167]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.builtin_core(EvalOp::Pow, &[v163, v168]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v169)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_74_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v156 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match eo__24eo_5ftypeof(s, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match eo__24bv_5fbitwidth(s, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.builtin_core(EvalOp::Add, &[v158, v159]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_core(EvalOp::IsNeg, &[v160]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match if_73_eo__24run_5fevaluate(s, v161, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v170)
}
Some(false) => {
let v171 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match eo__24eo_5ftypeof(s, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match eo__24bv_5fbitwidth(s, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.builtin_core(EvalOp::Add, &[v174, v175]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v171, v176) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v177)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_76_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v150 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match eo__24eo_5ftypeof(s, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match eo__24bv_5fbitwidth(s, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.builtin_core(EvalOp::Add, &[v152, v153]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.builtin_core(EvalOp::IsZ, &[v154]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match if_74_eo__24run_5fevaluate(s, v155, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_core(EvalOp::Neg, &[v178]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match eo__24eo_5ftypeof(s, v182) { Ok(v) => v, Err(e) => return Err(e) };
more_75_eo__24run_5fevaluate(s, v183, v180, v181, v179)
}
Some(false) => {
let v190 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24eo_5ftypeof(s, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match eo__24bv_5fbitwidth(s, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.builtin_core(EvalOp::Add, &[v194, v195]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_core(EvalOp::Extract, &[v190, v191, v196]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.builtin_core(EvalOp::ToInt, &[v197]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v198)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_77_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v226 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v226)
}
Some(false) => {
let v227 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match eo__24eo_5ftypeof(s, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match eo__24bv_5fbitwidth(s, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.builtin_core(EvalOp::Add, &[v230, v231]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.builtin_core(EvalOp::Pow, &[v227, v232]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v233)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_78_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v220 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match eo__24eo_5ftypeof(s, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24bv_5fbitwidth(s, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.builtin_core(EvalOp::Add, &[v222, v223]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.builtin_core(EvalOp::IsNeg, &[v224]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match if_77_eo__24run_5fevaluate(s, v225, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v234)
}
Some(false) => {
let v235 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match eo__24eo_5ftypeof(s, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match eo__24bv_5fbitwidth(s, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.builtin_core(EvalOp::Add, &[v238, v239]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v235, v240) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v241)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_80_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v214 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match eo__24eo_5ftypeof(s, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match eo__24bv_5fbitwidth(s, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.builtin_core(EvalOp::Add, &[v216, v217]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.builtin_core(EvalOp::IsZ, &[v218]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match if_78_eo__24run_5fevaluate(s, v219, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.builtin_core(EvalOp::Neg, &[v242]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match eo__24eo_5ftypeof(s, v246) { Ok(v) => v, Err(e) => return Err(e) };
more_79_eo__24run_5fevaluate(s, v247, v244, v245, v243)
}
Some(false) => {
let v254 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match eo__24eo_5ftypeof(s, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match eo__24bv_5fbitwidth(s, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.builtin_core(EvalOp::Add, &[v258, v259]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.builtin_core(EvalOp::Extract, &[v254, v255, v260]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.builtin_core(EvalOp::ToInt, &[v261]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v262)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_85_eo__24run_5fevaluate(s: &mut Store, v208: Term, v209: Term, v200: Term, v205: Term, v2: Term, v199: Term, v135: Term) -> CheckResult<Option<Term>> {
let v210 = match s.builtin_core(EvalOp::Add, &[v208, v209]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.builtin_core(EvalOp::Extract, &[v200, v205, v210]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_core(EvalOp::Eq, &[v211, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match if_80_eo__24run_5fevaluate(s, v213, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.builtin_core(EvalOp::Eq, &[v199, v263]) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.builtin_core(EvalOp::Or, &[v135, v264]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v265))
}
pub(super) fn more_84_eo__24run_5fevaluate(s: &mut Store, v147: Term, v148: Term, v5: Term, v2: Term, v135: Term) -> CheckResult<Option<Term>> {
let v149 = match s.builtin_core(EvalOp::Eq, &[v147, v148]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match if_76_eo__24run_5fevaluate(s, v149, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match eo__24eo_5ftypeof(s, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match eo__24bv_5fbitwidth(s, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.builtin_core(EvalOp::Add, &[v203, v204]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match eo__24eo_5ftypeof(s, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match eo__24bv_5fbitwidth(s, v207) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_85_eo__24run_5fevaluate(s, v208, v209, v200, v205, v2, v199, v135)
}
pub(super) fn more_83_eo__24run_5fevaluate(s: &mut Store, v5: Term, v136: Term, v2: Term, v135: Term) -> CheckResult<Option<Term>> {
let v137 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match eo__24eo_5ftypeof(s, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match eo__24bv_5fbitwidth(s, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_core(EvalOp::Add, &[v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match eo__24eo_5ftypeof(s, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match eo__24bv_5fbitwidth(s, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.builtin_core(EvalOp::Add, &[v144, v145]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_core(EvalOp::Extract, &[v136, v141, v146]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_84_eo__24run_5fevaluate(s, v147, v148, v5, v2, v135)
}
pub(super) fn more_82_eo__24run_5fevaluate(s: &mut Store, v74: Term, v75: Term, v5: Term, v71: Term, v70: Term, v2: Term) -> CheckResult<Option<Term>> {
let v76 = match s.builtin_core(EvalOp::Add, &[v74, v75]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match eo__24eo_5ftypeof(s, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match eo__24bv_5fbitwidth(s, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_core(EvalOp::Add, &[v79, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::Extract, &[v71, v76, v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_core(EvalOp::Eq, &[v82, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match if_72_eo__24run_5fevaluate(s, v84, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_core(EvalOp::Gt, &[v70, v134]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_83_eo__24run_5fevaluate(s, v5, v136, v2, v135)
}
pub(super) fn more_81_eo__24run_5fevaluate(s: &mut Store, v14: Term, v7: Term, v12: Term, v2: Term, v5: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Add, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Extract, &[v7, v12, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Eq, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match if_68_eo__24run_5fevaluate(s, v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24bv_5fbitwidth(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_82_eo__24run_5fevaluate(s, v74, v75, v5, v71, v70, v2)
}
pub(super) fn if_86_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5ftypeof(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24bv_5fbitwidth(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Add, &[v37, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Pow, &[v34, v39]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_87_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5ftypeof(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24bv_5fbitwidth(s, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::Add, &[v29, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::IsNeg, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match if_86_eo__24run_5fevaluate(s, v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
Some(false) => {
let v42 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5ftypeof(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match eo__24bv_5fbitwidth(s, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Add, &[v45, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v42, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v48)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_89_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v21 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24bv_5fbitwidth(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Add, &[v23, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::IsZ, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match if_87_eo__24run_5fevaluate(s, v26, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::Neg, &[v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5ftypeof(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_88_eo__24run_5fevaluate(s, v54, v51, v52, v50)
}
Some(false) => {
let v61 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24eo_5ftypeof(s, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24bv_5fbitwidth(s, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_core(EvalOp::Add, &[v65, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_core(EvalOp::Extract, &[v61, v62, v67]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::ToInt, &[v68]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v69)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_90_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v97 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v97)
}
Some(false) => {
let v98 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match eo__24eo_5ftypeof(s, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match eo__24bv_5fbitwidth(s, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.builtin_core(EvalOp::Add, &[v101, v102]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.builtin_core(EvalOp::Pow, &[v98, v103]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v104)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_91_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v91 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24eo_5ftypeof(s, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24bv_5fbitwidth(s, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.builtin_core(EvalOp::Add, &[v93, v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.builtin_core(EvalOp::IsNeg, &[v95]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match if_90_eo__24run_5fevaluate(s, v96, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v105)
}
Some(false) => {
let v106 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match eo__24eo_5ftypeof(s, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match eo__24bv_5fbitwidth(s, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.builtin_core(EvalOp::Add, &[v109, v110]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v106, v111) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v112)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_93_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v85 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24eo_5ftypeof(s, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24bv_5fbitwidth(s, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_core(EvalOp::Add, &[v87, v88]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_core(EvalOp::IsZ, &[v89]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match if_91_eo__24run_5fevaluate(s, v90, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.builtin_core(EvalOp::Neg, &[v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match eo__24eo_5ftypeof(s, v117) { Ok(v) => v, Err(e) => return Err(e) };
more_92_eo__24run_5fevaluate(s, v118, v115, v116, v114)
}
Some(false) => {
let v125 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match eo__24eo_5ftypeof(s, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24bv_5fbitwidth(s, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_core(EvalOp::Add, &[v129, v130]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_core(EvalOp::Extract, &[v125, v126, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_core(EvalOp::ToInt, &[v132]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v133)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_95_eo__24run_5fevaluate(s: &mut Store, v74: Term, v75: Term, v2: Term, v71: Term, v70: Term) -> CheckResult<Option<Term>> {
let v76 = match s.builtin_core(EvalOp::Add, &[v74, v75]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match eo__24eo_5ftypeof(s, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match eo__24bv_5fbitwidth(s, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_core(EvalOp::Add, &[v79, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::Extract, &[v71, v76, v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_core(EvalOp::Eq, &[v82, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match if_93_eo__24run_5fevaluate(s, v84, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_core(EvalOp::Gt, &[v70, v134]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v135))
}
pub(super) fn more_94_eo__24run_5fevaluate(s: &mut Store, v14: Term, v7: Term, v12: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Add, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Extract, &[v7, v12, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Eq, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match if_89_eo__24run_5fevaluate(s, v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24bv_5fbitwidth(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_95_eo__24run_5fevaluate(s, v74, v75, v2, v71, v70)
}
pub(super) fn if_96_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5ftypeof(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24bv_5fbitwidth(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Add, &[v37, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Pow, &[v34, v39]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_97_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5ftypeof(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24bv_5fbitwidth(s, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::Add, &[v29, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::IsNeg, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match if_96_eo__24run_5fevaluate(s, v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
Some(false) => {
let v42 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5ftypeof(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match eo__24bv_5fbitwidth(s, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Add, &[v45, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v42, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v48)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_99_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v21 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24bv_5fbitwidth(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Add, &[v23, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::IsZ, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match if_97_eo__24run_5fevaluate(s, v26, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::Neg, &[v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5ftypeof(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_98_eo__24run_5fevaluate(s, v54, v51, v52, v50)
}
Some(false) => {
let v61 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24eo_5ftypeof(s, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24bv_5fbitwidth(s, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_core(EvalOp::Add, &[v65, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_core(EvalOp::Extract, &[v61, v62, v67]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::ToInt, &[v68]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v69)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_100_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v97 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v97)
}
Some(false) => {
let v98 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match eo__24eo_5ftypeof(s, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match eo__24bv_5fbitwidth(s, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.builtin_core(EvalOp::Add, &[v101, v102]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.builtin_core(EvalOp::Pow, &[v98, v103]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v104)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_101_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v91 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24eo_5ftypeof(s, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24bv_5fbitwidth(s, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.builtin_core(EvalOp::Add, &[v93, v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.builtin_core(EvalOp::IsNeg, &[v95]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match if_100_eo__24run_5fevaluate(s, v96, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v105)
}
Some(false) => {
let v106 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match eo__24eo_5ftypeof(s, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match eo__24bv_5fbitwidth(s, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.builtin_core(EvalOp::Add, &[v109, v110]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v106, v111) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v112)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_103_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v85 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24eo_5ftypeof(s, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24bv_5fbitwidth(s, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_core(EvalOp::Add, &[v87, v88]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_core(EvalOp::IsZ, &[v89]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match if_101_eo__24run_5fevaluate(s, v90, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.builtin_core(EvalOp::Neg, &[v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match eo__24eo_5ftypeof(s, v117) { Ok(v) => v, Err(e) => return Err(e) };
more_102_eo__24run_5fevaluate(s, v118, v115, v116, v114)
}
Some(false) => {
let v125 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match eo__24eo_5ftypeof(s, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24bv_5fbitwidth(s, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_core(EvalOp::Add, &[v129, v130]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_core(EvalOp::Extract, &[v125, v126, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_core(EvalOp::ToInt, &[v132]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v133)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_104_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v162 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v162)
}
Some(false) => {
let v163 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match eo__24eo_5ftypeof(s, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match eo__24bv_5fbitwidth(s, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.builtin_core(EvalOp::Add, &[v166, v167]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.builtin_core(EvalOp::Pow, &[v163, v168]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v169)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_105_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v156 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match eo__24eo_5ftypeof(s, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match eo__24bv_5fbitwidth(s, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.builtin_core(EvalOp::Add, &[v158, v159]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_core(EvalOp::IsNeg, &[v160]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match if_104_eo__24run_5fevaluate(s, v161, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v170)
}
Some(false) => {
let v171 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match eo__24eo_5ftypeof(s, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match eo__24bv_5fbitwidth(s, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.builtin_core(EvalOp::Add, &[v174, v175]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v171, v176) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v177)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_107_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v150 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match eo__24eo_5ftypeof(s, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match eo__24bv_5fbitwidth(s, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.builtin_core(EvalOp::Add, &[v152, v153]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.builtin_core(EvalOp::IsZ, &[v154]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match if_105_eo__24run_5fevaluate(s, v155, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_core(EvalOp::Neg, &[v178]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match eo__24eo_5ftypeof(s, v182) { Ok(v) => v, Err(e) => return Err(e) };
more_106_eo__24run_5fevaluate(s, v183, v180, v181, v179)
}
Some(false) => {
let v190 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24eo_5ftypeof(s, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match eo__24bv_5fbitwidth(s, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.builtin_core(EvalOp::Add, &[v194, v195]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_core(EvalOp::Extract, &[v190, v191, v196]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.builtin_core(EvalOp::ToInt, &[v197]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v198)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_108_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v226 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v226)
}
Some(false) => {
let v227 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match eo__24eo_5ftypeof(s, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match eo__24bv_5fbitwidth(s, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.builtin_core(EvalOp::Add, &[v230, v231]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.builtin_core(EvalOp::Pow, &[v227, v232]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v233)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_109_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v220 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match eo__24eo_5ftypeof(s, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24bv_5fbitwidth(s, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.builtin_core(EvalOp::Add, &[v222, v223]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.builtin_core(EvalOp::IsNeg, &[v224]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match if_108_eo__24run_5fevaluate(s, v225, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v234)
}
Some(false) => {
let v235 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match eo__24eo_5ftypeof(s, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match eo__24bv_5fbitwidth(s, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.builtin_core(EvalOp::Add, &[v238, v239]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v235, v240) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v241)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_111_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v214 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match eo__24eo_5ftypeof(s, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match eo__24bv_5fbitwidth(s, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.builtin_core(EvalOp::Add, &[v216, v217]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.builtin_core(EvalOp::IsZ, &[v218]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match if_109_eo__24run_5fevaluate(s, v219, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.builtin_core(EvalOp::Neg, &[v242]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match eo__24eo_5ftypeof(s, v246) { Ok(v) => v, Err(e) => return Err(e) };
more_110_eo__24run_5fevaluate(s, v247, v244, v245, v243)
}
Some(false) => {
let v254 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match eo__24eo_5ftypeof(s, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match eo__24bv_5fbitwidth(s, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.builtin_core(EvalOp::Add, &[v258, v259]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.builtin_core(EvalOp::Extract, &[v254, v255, v260]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.builtin_core(EvalOp::ToInt, &[v261]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v262)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_116_eo__24run_5fevaluate(s: &mut Store, v208: Term, v209: Term, v200: Term, v205: Term, v2: Term, v199: Term, v135: Term) -> CheckResult<Option<Term>> {
let v210 = match s.builtin_core(EvalOp::Add, &[v208, v209]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.builtin_core(EvalOp::Extract, &[v200, v205, v210]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_core(EvalOp::Eq, &[v211, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match if_111_eo__24run_5fevaluate(s, v213, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.builtin_core(EvalOp::Eq, &[v199, v263]) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.builtin_core(EvalOp::Or, &[v135, v264]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v265))
}
pub(super) fn more_115_eo__24run_5fevaluate(s: &mut Store, v147: Term, v148: Term, v5: Term, v2: Term, v135: Term) -> CheckResult<Option<Term>> {
let v149 = match s.builtin_core(EvalOp::Eq, &[v147, v148]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match if_107_eo__24run_5fevaluate(s, v149, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match eo__24eo_5ftypeof(s, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match eo__24bv_5fbitwidth(s, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.builtin_core(EvalOp::Add, &[v203, v204]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match eo__24eo_5ftypeof(s, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match eo__24bv_5fbitwidth(s, v207) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_116_eo__24run_5fevaluate(s, v208, v209, v200, v205, v2, v199, v135)
}
pub(super) fn more_114_eo__24run_5fevaluate(s: &mut Store, v5: Term, v136: Term, v2: Term, v135: Term) -> CheckResult<Option<Term>> {
let v137 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match eo__24eo_5ftypeof(s, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match eo__24bv_5fbitwidth(s, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_core(EvalOp::Add, &[v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match eo__24eo_5ftypeof(s, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match eo__24bv_5fbitwidth(s, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.builtin_core(EvalOp::Add, &[v144, v145]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_core(EvalOp::Extract, &[v136, v141, v146]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_115_eo__24run_5fevaluate(s, v147, v148, v5, v2, v135)
}
pub(super) fn more_113_eo__24run_5fevaluate(s: &mut Store, v74: Term, v75: Term, v2: Term, v71: Term, v70: Term, v5: Term) -> CheckResult<Option<Term>> {
let v76 = match s.builtin_core(EvalOp::Add, &[v74, v75]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match eo__24eo_5ftypeof(s, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match eo__24bv_5fbitwidth(s, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_core(EvalOp::Add, &[v79, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::Extract, &[v71, v76, v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_core(EvalOp::Eq, &[v82, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match if_103_eo__24run_5fevaluate(s, v84, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_core(EvalOp::Gt, &[v70, v134]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_114_eo__24run_5fevaluate(s, v5, v136, v2, v135)
}
pub(super) fn more_112_eo__24run_5fevaluate(s: &mut Store, v14: Term, v7: Term, v12: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Add, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Extract, &[v7, v12, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Eq, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match if_99_eo__24run_5fevaluate(s, v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24bv_5fbitwidth(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_113_eo__24run_5fevaluate(s, v74, v75, v2, v71, v70, v5)
}
pub(super) fn if_117_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v26 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
Some(false) => {
let v27 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::ToInt, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Pow, &[v27, v29]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_118_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::ToInt, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::IsNeg, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match if_117_eo__24run_5fevaluate(s, v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
Some(false) => {
let v32 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::ToInt, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v35)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_119_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::ToBin, &[v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24bv_5fbitwidth(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::ToInt, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::ToInt, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsZ, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match if_118_eo__24run_5fevaluate(s, v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::Mul, &[v19, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_core(EvalOp::ToBin, &[v17, v37]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_120_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v26 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
Some(false) => {
let v27 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::ToInt, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Pow, &[v27, v29]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_121_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::ToInt, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::IsNeg, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match if_120_eo__24run_5fevaluate(s, v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
Some(false) => {
let v32 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::ToInt, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v35)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_122_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::ToBin, &[v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24bv_5fbitwidth(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::ToInt, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::ToInt, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsZ, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match if_121_eo__24run_5fevaluate(s, v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::IntDiv, &[v19, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_core(EvalOp::ToBin, &[v17, v37]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_123_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v35)
}
Some(false) => {
let v36 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5ftypeof(s, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24bv_5fbitwidth(s, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_core(EvalOp::Add, &[v39, v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_core(EvalOp::Pow, &[v36, v41]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_124_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5ftypeof(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24bv_5fbitwidth(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::Add, &[v31, v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::IsNeg, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match if_123_eo__24run_5fevaluate(s, v34, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
Some(false) => {
let v44 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match eo__24eo_5ftypeof(s, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24bv_5fbitwidth(s, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::Add, &[v47, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v44, v49) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v50)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_126_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5ftypeof(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24bv_5fbitwidth(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Add, &[v25, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::IsZ, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match if_124_eo__24run_5fevaluate(s, v28, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_core(EvalOp::Neg, &[v51]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24eo_5ftypeof(s, v55) { Ok(v) => v, Err(e) => return Err(e) };
more_125_eo__24run_5fevaluate(s, v56, v53, v54, v52)
}
Some(false) => {
let v63 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24eo_5ftypeof(s, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match eo__24bv_5fbitwidth(s, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::Add, &[v67, v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_core(EvalOp::Extract, &[v63, v64, v69]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.builtin_core(EvalOp::ToInt, &[v70]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v71)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_127_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v79 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v79)
}
Some(false) => {
let v80 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::ToInt, &[v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_core(EvalOp::Pow, &[v80, v82]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v83)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_128_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v76 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.builtin_core(EvalOp::ToInt, &[v76]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_core(EvalOp::IsNeg, &[v77]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match if_127_eo__24run_5fevaluate(s, v78, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v84)
}
Some(false) => {
let v85 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.builtin_core(EvalOp::ToInt, &[v86]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v85, v87) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v88)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_130_eo__24run_5fevaluate(s: &mut Store, v75: Term, v2: Term, v72: Term, v8: Term) -> CheckResult<Option<Term>> {
let v89 = match if_128_eo__24run_5fevaluate(s, v75, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_core(EvalOp::IntDiv, &[v72, v89]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.builtin_core(EvalOp::ToBin, &[v8, v90]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v91))
}
pub(super) fn more_129_eo__24run_5fevaluate(s: &mut Store, v5: Term, v9: Term, v14: Term, v2: Term, v8: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24run_5fevaluate(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5ftypeof(s, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24bv_5fbitwidth(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Add, &[v17, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Extract, &[v9, v14, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Eq, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match if_126_eo__24run_5fevaluate(s, v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_core(EvalOp::ToInt, &[v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_core(EvalOp::IsZ, &[v74]) { Ok(v) => v, Err(e) => return Err(e) };
more_130_eo__24run_5fevaluate(s, v75, v2, v72, v8)
}
pub(super) fn if_131_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24run_5fevaluate(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListRepeat, &[v11, v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24bv_5feval_5fconcat(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match eo__24run_5fevaluate(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_repeat, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_132_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v36 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
Some(false) => {
let v37 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5ftypeof(s, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24bv_5fbitwidth(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_core(EvalOp::Add, &[v40, v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_core(EvalOp::Pow, &[v37, v42]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_133_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v30 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5ftypeof(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24bv_5fbitwidth(s, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::Add, &[v32, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_core(EvalOp::IsNeg, &[v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_132_eo__24run_5fevaluate(s, v35, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
Some(false) => {
let v45 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24eo_5ftypeof(s, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match eo__24bv_5fbitwidth(s, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::Add, &[v48, v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v45, v50) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v51)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_135_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5ftypeof(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24bv_5fbitwidth(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Add, &[v26, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::IsZ, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match if_133_eo__24run_5fevaluate(s, v29, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_core(EvalOp::Neg, &[v52]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match eo__24eo_5ftypeof(s, v56) { Ok(v) => v, Err(e) => return Err(e) };
more_134_eo__24run_5fevaluate(s, v57, v54, v55, v53)
}
Some(false) => {
let v64 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match eo__24eo_5ftypeof(s, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24bv_5fbitwidth(s, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_core(EvalOp::Add, &[v68, v69]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.builtin_core(EvalOp::Extract, &[v64, v65, v70]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.builtin_core(EvalOp::ToInt, &[v71]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v72)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_136_eo__24run_5fevaluate(s: &mut Store, v13: Term, v14: Term, v2: Term, v10: Term, v9: Term) -> CheckResult<Option<Term>> {
let v15 = match s.builtin_core(EvalOp::Add, &[v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fbitwidth(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Add, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Extract, &[v10, v15, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match if_135_eo__24run_5fevaluate(s, v23, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_core(EvalOp::ToBin, &[v9, v73]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v74))
}
pub(super) fn if_137_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5ftypeof(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24bv_5fbitwidth(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_core(EvalOp::Pow, &[v34, v37]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_138_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5ftypeof(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24bv_5fbitwidth(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::IsNeg, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match if_137_eo__24run_5fevaluate(s, v32, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v39)
}
Some(false) => {
let v40 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5ftypeof(s, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24bv_5fbitwidth(s, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_139_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v21 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::ToInt, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
Some(false) => {
let v23 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::ToInt, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24run_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5ftypeof(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24bv_5fbitwidth(s, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::IsZ, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match if_138_eo__24run_5fevaluate(s, v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_core(EvalOp::Neg, &[v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Add, &[v24, v46]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v47)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_140_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24bv_5fbitwidth(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Add, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Extract, &[v2, v13, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Eq, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match if_139_eo__24run_5fevaluate(s, v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v48)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fprog_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24run_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fprog_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fevaluate(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_evaluate"
pub fn eo__24eo_5fprog_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fevaluate(s, a0);
s.leave();
result
}
pub(super) fn case_611_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eevaluate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fevaluate(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_152_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_608_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_609_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_610_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_611_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fprog_5fdistinct_5fvalues(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24are_5fdistinct_5fterms_5ftype(s, a0, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24eo_5fprog_5fdistinct_5fvalues(s: &mut Store, v4: Term, v5: Term, a0: Term, a1: Term) -> CheckResult<Term> {
if v4 != v5 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn case_0_eo__24eo_5fprog_5fdistinct_5fvalues(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::Eq, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match if_0_eo__24eo_5fprog_5fdistinct_5fvalues(s, v0, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_1_eo__24eo_5fprog_5fdistinct_5fvalues(s, v4, v5, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fdistinct_5fvalues(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdistinct_5fvalues(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_distinct_values"
pub fn eo__24eo_5fprog_5fdistinct_5fvalues(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdistinct_5fvalues(s, a0, a1);
s.leave();
result
}
pub(super) fn case_612_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edistinct_5fvalues, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = fields[1];
let v7 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fprog_5fdistinct_5fvalues(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_1_eo__24get_5fai_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if a2 != a1 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn case_2_eo__24get_5fai_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.apply(a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$get_ai_norm_rec"
pub fn eo__24get_5fai_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(889), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5fai_5fnorm_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(889), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24get_5fai_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5fai_5fnorm_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24get_5fai_5fnorm_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24get_5fai_5fnorm_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24get_5fai_5fnorm_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match eo__24get_5fai_5fnorm_5frec(s, a0, a1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24get_5fai_5fnorm_5frec(s, a0, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListConcat, &[a0, v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListSetof, &[a0, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24get_5fai_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v12 = match eo__24get_5fai_5fnorm_5frec(s, v4, v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonElim, &[v4, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24get_5fai_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5fai_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$get_ai_norm"
pub fn eo__24get_5fai_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24get_5fai_5fnorm(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24get_5fai_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_1_eo__24get_5faci_5fnormal_5fform(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40aci_5fsorted, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24get_5fai_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
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
match s.cached_program(ProgramId(886), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5fa_5fnorm_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(886), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn case_613_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
match s.cached_program(ProgramId(901), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fabsorb_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(901), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn case_614_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_615_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_153_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_612_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_613_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_614_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_615_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_616_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_154_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_616_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_38_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_152_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_153_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_154_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
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
match s.cached_program(ProgramId(988), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdecl_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(988), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(990), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(990), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(992), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(992), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(998), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5finhabited_5ftype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(998), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(986), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdd_5fhas_5fdt(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(986), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(989), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdecl_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(989), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(991), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(991), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(995), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(995), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(1003), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftype_5fwf_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1003), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(1001), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftype_5fwf(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1001), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(749), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(749), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(750), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(750), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(751), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(751), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(772), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5ftype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(772), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_to_smt_lambda_curry"
pub fn eo__24eo_5fto_5fsmt_5flambda_5fcurry(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(755), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(755), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v13 = match eo__24smtx_5ftype_5fwf_5fcomponent(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s, v13, v9, v2, a1, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry(s: &mut Store, condition: Term, v9: Term, v2: Term, a1: Term, v11: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v14 = match eo__24eo_5fto_5fsmt_5ftype(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5fto_5fsmt_5flambda_5fcurry(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5fsm_2elam, &[v11, v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
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
pub(super) fn case_0_eo__24smtx_5ftypeof_5fbindings(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsbd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
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
pub(super) fn case_13_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
pub(super) fn case_79_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
pub(super) fn case_104_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_105_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_106_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
pub(super) fn case_127_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
match s.cached_program(ProgramId(987), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdd_5flookup(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(987), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(997), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdtc_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(997), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(994), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(994), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(1016), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1016), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(1000), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1000), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
