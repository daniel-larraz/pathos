//! Generated functions, module 12 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
// EO program "$eo_to_smt"
pub fn eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(737), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(737), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match cases_2_0_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_1_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_2_2_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_9_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_10_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2enot, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_11_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_12_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eand, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_13_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d_3e, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_14_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2exor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_15_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_16_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Teq, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_2_eo__24eo_5fto_5fsmt(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_17_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2e_40purify, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_18_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_2b, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_19_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_2d, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_20_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_2a, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_21_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3c, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_22_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3c_3d, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_23_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3e, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_24_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3e_3d, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_25_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eto_5freal, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_26_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eto_5fint, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_27_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_is_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eis_5fint, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_28_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eabs, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_29_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2euneg, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_30_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ediv, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_31_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2emod, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_32_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_divisible, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2edivisible, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_33_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eint_2epow2, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_34_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eint_2elog2, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_35_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2e_3e_3d, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2eint_2elog2, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eint_2epow2, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v8, v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fto_5fsmt(s, v7, v12)
}
pub(super) fn case_36_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ediv_5ftotal, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_37_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2emod_5ftotal, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_38_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40int_5fdiv_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2ediv, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_39_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40mod_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2emod, &[v4, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_40_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eselect, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_41_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estore, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_42_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40array_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff(s, v7, v9, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_43_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt_5fbv_5fsize(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Zleq, &[v4, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_4_eo__24eo_5fto_5fsmt(s, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_44_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2econcat, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_45_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_extract, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eextract, &[v6, v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_46_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_repeat, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2erepeat, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_47_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ebvnot, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_48_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvand, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_49_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_50_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvnand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvnand, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_51_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvnor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvnor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_52_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvxor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_53_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxnor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvxnor, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_54_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvcomp, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_55_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ebvneg, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_56_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvadd, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_57_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvmul, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_58_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvudiv, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_59_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvurem, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_60_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsub, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_61_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsdiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsdiv, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_62_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsrem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsrem, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_63_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsmod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsmod, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_64_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvult, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_65_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvule, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_66_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvugt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvugt, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_67_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvuge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvuge, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_68_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvslt, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_69_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsle, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_70_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsgt, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_71_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsge, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_72_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvshl, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_73_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvlshr, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_74_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvashr, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_75_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_zero_5fextend, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2ezero_5fextend, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_76_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_sign_5fextend, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2esign_5fextend, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_77_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_rotate_5fleft, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2erotate_5fleft, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_78_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_rotate_5fright, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2erotate_5fright, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_79_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v10, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fto_5fsmt(s, v14, v15, v16)
}
pub(super) fn case_80_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvuaddo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvuaddo, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_81_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvnego, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ebvnego, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_82_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsaddo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsaddo, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_83_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvumulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvumulo, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_84_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsmulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsmulo, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_85_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvusubo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvusubo, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_86_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvssubo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvssubo, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_87_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsdivo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvsdivo, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_88_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvultbv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvult, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fto_5fsmt(s, v13, v14, v9, v12)
}
pub(super) fn case_89_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsltbv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ebvslt, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fto_5fsmt(s, v13, v14, v9, v12)
}
pub(super) fn case_90_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvredand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt_5fbv_5fsize(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2ebvnot, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2ebvcomp, &[v4, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_91_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvredor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt_5fbv_5fsize(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2ebvcomp, &[v4, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2ebvnot, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_92_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo__40bit, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eextract, &[v5, v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v8, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_93_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fto_5fsmt(s, v8, v11, v14, v7)
}
pub(super) fn case_95_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_96_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2e_2b_2b, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_97_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_98_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2econtains, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_99_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_100_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eindexof, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_101_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eat, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_102_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eprefixof, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_103_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2esuffixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esuffixof, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_104_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2erev, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_105_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eupdate, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_106_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eto_5flower, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_107_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eto_5fupper, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_108_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eto_5fcode, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_109_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2efrom_5fcode, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_110_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eis_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eis_5fdigit, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_111_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eto_5fint, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_112_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2efrom_5fint, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_113_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2e_3c, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_114_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2e_3c_3d, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_115_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fall, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_116_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fre, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_117_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fre_5fall, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_118_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eindexof_5fre, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_122_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eto_5fre, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_123_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2e_2a, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_124_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2e_2b, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_125_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_re_2e_5e, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2e_5e, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_126_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2eopt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eopt, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_127_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2ecomp, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_128_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2erange, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_129_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2e_2b_2b, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_130_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2einter, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_131_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eunion, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_132_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2ediff, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_133_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_re_2eloop, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eloop, &[v6, v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_134_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ein_5fre, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_135_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eseq_2eunit, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_136_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eseq_2enth, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_137_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40re_5funfold_5fpos_5fcomponent, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_9_eo__24eo_5fto_5fsmt(s, v4, v1, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_138_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eseq_5fdiff, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_139_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fto_5fsmt(s, v14, v2, v13, v10, v12)
}
pub(super) fn case_140_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.raw(Lit::Str(EoString::from_code_points(vec![48,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eString, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.raw(Lit::Str(EoString::from_code_points(vec![57,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eString, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2erange, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2ecomp, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2ere_2einter, &[v5, v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fto_5fsmt(s, v4, v12)
}
pub(super) fn case_141_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2efrom_5fint, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fto_5fsmt(s, v2, v14, v10, v12)
}
pub(super) fn case_142_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v9, v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fto_5fsmt(s, v7, v8, v14, v5, v2)
}
pub(super) fn case_143_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v9, v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fto_5fsmt(s, v7, v8, v14, v5, v2)
}
pub(super) fn case_144_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2e_40strings_5foccur_5findex, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_145_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_146_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match eo__24eo_5fto_5fsmt(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fto_5fsmt(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2e_40strings_5foccur_5findex, &[v14, v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5fto_5fsmt(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24eo_5fto_5fsmt(s, v18, v13, v17, v8, v5)
}
pub(super) fn case_147_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match eo__24eo_5fto_5fsmt(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fto_5fsmt(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre, &[v14, v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5fto_5fsmt(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24eo_5fto_5fsmt(s, v18, v13, v17, v8, v5)
}
pub(super) fn case_148_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40witness_5fstring_5flength, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_20_eo__24eo_5fto_5fsmt(s, v4, v3, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_149_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_is, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt_5ftester(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_150_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match eo__24eo_5fto_5fsmt(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt_5fupdater(s, v8, v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_152_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt_5ftuple_5fprepend(s, v7, v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_153_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_tuple_2eselect, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5ftuple_5fselect(s, v6, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_154_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt_5ftuple_5fupdate(s, v9, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_156_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2esingleton, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_157_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2eunion, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_158_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2einter, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_159_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eminus, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2eminus, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_160_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2emember, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_161_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2esubset, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2esubset, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_162_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2echoose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2eempty, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2emap_5fdiff, &[v4, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_163_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2eis_5fempty, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2eempty, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v4, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_164_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2eis_5fsingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5fset_5felem_5ftype(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2eempty, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2emap_5fdiff, &[v5, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2esingleton, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v4, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_165_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2einsert, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2esingleton, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2eset_2eunion, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_166_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40sets_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff(s, v7, v9, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_167_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_2f, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_168_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_2f_5ftotal, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_169_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40div_5fby_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.raw(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::MkRational, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eRational, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_2f, &[v4, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_171_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2enot, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5fexists(s, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2enot, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_173_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5fexists(s, v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_174_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__40quantifiers_5fskolemize, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_21_eo__24eo_5fto_5fsmt(s, v10, v5, v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_175_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_int_5fto_5fbv, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eint_5fto_5fbv, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_176_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eubv_5fto_5fint, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_177_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_sbv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2esbv_5fto_5fint, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_179_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24eo_5fto_5fsmt(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_2_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_3_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_4_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_5_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_20_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_21_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_22_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_23_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_6_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_24_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_25_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_26_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_27_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_7_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_28_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_29_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_30_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_31_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_8_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_32_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_33_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_34_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_35_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_9_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_36_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_37_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_38_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_39_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_10_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_40_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_41_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_42_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_43_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_11_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_44_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_45_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_46_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_47_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_12_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_48_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_49_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_50_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_51_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_13_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_52_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_53_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_54_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_55_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_14_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_56_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_57_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_58_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_59_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_15_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_60_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_61_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_62_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_63_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_16_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_64_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_65_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_66_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_67_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_17_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_68_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_69_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_70_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_71_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_18_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_72_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_73_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_74_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_75_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_19_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_76_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_77_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_78_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_79_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_20_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_80_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_81_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_82_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_83_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_21_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_84_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_85_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_86_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_87_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_22_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_88_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_89_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_90_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_91_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_23_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_92_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_93_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_94_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_95_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_24_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_96_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_97_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_98_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_99_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_25_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_100_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_101_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_102_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_103_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_26_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_104_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_105_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_106_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_107_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_27_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_108_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_109_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_110_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_111_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_28_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_112_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_113_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_114_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_115_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_29_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_116_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_117_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_118_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_119_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_30_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_120_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_121_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_122_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_123_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_31_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_124_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_125_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_126_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_127_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_32_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_128_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_129_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_130_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_131_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_33_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_132_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_133_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_134_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_135_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_34_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_136_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_137_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_138_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_139_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_35_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_140_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_141_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_142_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_143_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_36_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_144_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_145_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_146_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_147_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_37_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_148_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_149_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_150_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_151_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_38_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_152_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_153_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_154_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_155_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_39_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_156_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_157_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_158_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_159_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_40_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_160_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_161_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_162_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_163_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_41_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_164_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_165_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_166_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_167_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_42_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_168_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_169_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_170_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_171_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_43_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_172_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_173_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_174_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_175_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_44_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_176_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_177_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_178_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_179_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_6_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_7_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_2_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_8_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_9_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_10_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_11_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_3_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_12_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_13_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_14_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_15_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_4_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_16_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_17_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_18_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_19_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_5_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_20_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_21_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_22_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_23_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_6_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_24_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_25_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_26_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_27_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_7_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_28_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_29_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_30_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_31_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_8_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_32_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_33_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_34_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_35_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_9_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_36_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_37_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_38_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_39_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_10_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_40_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_41_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_42_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_43_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_11_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_44_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_45_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_0_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_0_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_1_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_2_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_3_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_1_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_4_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_5_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_6_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_7_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_2_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_8_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_9_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_10_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_11_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_2_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match eo__24eo_5fto_5fsmt_5fdistinct(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24smtx_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fto_5fsmt_5fbv_5fsize(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2e_40purify, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v1: Term, v2: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match eo__24eo_5fto_5fsmt(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt_5fnat(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent(s, v5, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_10_eo__24eo_5fto_5fsmt(s: &mut Store, v14: Term, v2: Term, v13: Term, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v13, v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eto_5fint, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v10, v12, v18]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn more_12_eo__24eo_5fto_5fsmt(s: &mut Store, v2: Term, v14: Term, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v15 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v14, v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2eto_5fint, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24emb_5fsm_2eite, &[v10, v12, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn more_13_eo__24eo_5fto_5fsmt(s: &mut Store, v7: Term, v8: Term, v14: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fall, &[v7, v8, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v19, v21, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fall, &[v17, v18, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fto_5fsmt(s, v16, v26)
}
pub(super) fn more_15_eo__24eo_5fto_5fsmt(s: &mut Store, v7: Term, v8: Term, v14: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fre_5fall, &[v7, v8, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v19, v21, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fre_5fall, &[v17, v18, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fto_5fsmt(s, v16, v26)
}
pub(super) fn more_17_eo__24eo_5fto_5fsmt(s: &mut Store, v18: Term, v13: Term, v17: Term, v8: Term, v5: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v13, v17, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fall, &[v20, v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn more_18_eo__24eo_5fto_5fsmt(s: &mut Store, v18: Term, v13: Term, v17: Term, v8: Term, v5: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2esubstr, &[v13, v17, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5fto_5fsmt(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2ereplace_5fre_5fall, &[v20, v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn if_19_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2eVar, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2estr_2elen, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24emb_5fsm_2echoice, &[v6, v7, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_20_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v3: Term, v1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_19_eo__24eo_5fto_5fsmt(s, v5, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v5: Term, v2: Term, v8: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5fsm_2enot, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fto_5fsmt_5fnat(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize(s, v8, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
// EO program "$eo_to_smt_distinct"
pub fn eo__24eo_5fto_5fsmt_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(743), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdistinct(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(743), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdistinct(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdistinct(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5fdistinct(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdistinct(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5fdistinct(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fsm_2eand, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
// EO program "$eo_to_smt_distinct_pairs"
pub fn eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(744), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(744), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[a0, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2enot, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt_5fdistinct_5fpairs(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fsm_2eand, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
// EO program "$eo_to_smt_typed_list_elem_type"
pub fn eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(764), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(764), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::Teq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_1_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s, v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn if_1_eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
// The entry points of checking, to be called on the checker's stack (see
// front.rs): they call generated functions, and nothing generated calls
// them, so the generator puts them after all the generated functions.
impl Store {
    /// Check the entire proof state machine, including typing, assumptions,
    /// step-pop, premise lookup and the final closed refutation test. To be
    /// called on the checker's stack: see `Store::check_refutation`.
    pub(crate) fn check_refutation_inner(&mut self, assumptions: Term, commands: Term) -> CheckResult<bool> {
        self.calls = 0;
        let answer = generated::eo__24eo_5fchecker_5fis_5frefutation(self, assumptions, commands)?;
        self.is_native_true(answer)
    }
    /// The verdict on a proof. To be called on the checker's stack: see
    /// `Store::check_proof`.
    pub(crate) fn check_proof_inner(&mut self, assumptions: Term, commands: Term) -> CheckResult<Verdict> {
        if !self.check_refutation_inner(assumptions, commands)? {
            return Ok(Verdict::Incorrect);
        }
        if !true {
            return Ok(Verdict::Incomplete);
        }
        if !self.arguments_translate(assumptions, None)? {
            return Ok(Verdict::Incomplete);
        }
        let mut list = commands;
        loop {
            if self.is_node(list, Some(Constructor::eo__24emb_5fcmdl_2enil))? {
                return Ok(Verdict::Correct);
            }
            let Some(cs) = self.node_fields(list, Some(Constructor::eo__24emb_5fcmdl_2econs))? else {
                return Ok(Verdict::Incorrect);
            };
            let c = cs[0];
            if let Some(fs) = self.node_fields(c, Some(Constructor::eo__24emb_5fcmd_2eassume_5fpush))? {
                if !self.has_translation(fs[0])? {
                    return Ok(Verdict::Incomplete);
                }
            } else if let Some(fs) = self.node_fields(c, Some(Constructor::eo__24emb_5fcmd_2estep))? {
                let rule = match self.view(fs[0])? {
                    TermData::Node(rule, _) => *rule,
                    _ => return Ok(Verdict::Incorrect),
                };
                if !self.arguments_translate(fs[1], Some(rule))? {
                    return Ok(Verdict::Incomplete);
                }
            }
            list = cs[1];
        }
    }

    /// The number of arguments of a rule whose arguments have a mask.
    #[allow(clippy::match_single_binding)]
    fn mask_len(rule: Constructor) -> Option<usize> {
        match rule {
            Constructor::eo__24emb_5fr_2echain_5fresolution => Some(2),
Constructor::eo__24emb_5fr_2echain_5fm_5fresolution => Some(3),
Constructor::eo__24emb_5fr_2einstantiate => Some(1),
Constructor::eo__24emb_5fr_2ealpha_5fequiv => Some(3),
Constructor::eo__24emb_5fr_2edistinct_5fbinary_5felim => Some(2),
Constructor::eo__24emb_5fr_2eexists_5fstring_5flength => Some(3),
Constructor::eo__24emb_5fr_2esets_5feq_5fsingleton_5femp => Some(3),
Constructor::eo__24emb_5fr_2esets_5fmember_5femp => Some(3),
Constructor::eo__24emb_5fr_2esets_5finter_5femp1 => Some(3),
Constructor::eo__24emb_5fr_2esets_5finter_5femp2 => Some(3),
Constructor::eo__24emb_5fr_2esets_5fminus_5femp1 => Some(3),
Constructor::eo__24emb_5fr_2esets_5fminus_5femp2 => Some(3),
Constructor::eo__24emb_5fr_2esets_5funion_5femp1 => Some(3),
Constructor::eo__24emb_5fr_2esets_5funion_5femp2 => Some(3),
Constructor::eo__24emb_5fr_2esets_5fminus_5fself => Some(2),
Constructor::eo__24emb_5fr_2esets_5fis_5fempty_5felim => Some(2),
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange => Some(4),
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart => Some(4),
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg => Some(4),
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen => Some(6),
Constructor::eo__24emb_5fr_2estr_5fconcat_5funify_5fbase => Some(4),
Constructor::eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev => Some(4),
Constructor::eo__24emb_5fr_2estr_5fcontains_5fchar => Some(3),
Constructor::eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec => Some(4),
Constructor::eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase => Some(2),
Constructor::eo__24emb_5fr_2estr_5findexof_5fself => Some(3),
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen => Some(3),
Constructor::eo__24emb_5fr_2esets_5fmember_5fsingleton => Some(2),
Constructor::eo__24emb_5fr_2esets_5fchoose_5fsingleton => Some(1),
Constructor::eo__24emb_5fr_2eseq_5flen_5funit => Some(1),
Constructor::eo__24emb_5fr_2eseq_5frev_5funit => Some(1),
Constructor::eo__24emb_5fr_2eseq_5fnth_5funit => Some(1),

            _ => None,
        }
    }
    /// What the mask of `rule` asks of its `i`-th argument.
    #[allow(clippy::match_single_binding)]
    fn mask_kind(rule: Constructor, i: usize) -> Option<ArgKind> {
        match rule {
            Constructor::eo__24emb_5fr_2echain_5fresolution => match i {
0 => Some(ArgKind::List),
1 => Some(ArgKind::List),
_ => None,
},
Constructor::eo__24emb_5fr_2echain_5fm_5fresolution => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::List),
2 => Some(ArgKind::List),
_ => None,
},
Constructor::eo__24emb_5fr_2einstantiate => match i {
0 => Some(ArgKind::List),
_ => None,
},
Constructor::eo__24emb_5fr_2ealpha_5fequiv => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::List),
2 => Some(ArgKind::List),
_ => None,
},
Constructor::eo__24emb_5fr_2edistinct_5fbinary_5felim => match i {
0 => Some(ArgKind::WfTerm),
1 => Some(ArgKind::Term),
_ => None,
},
Constructor::eo__24emb_5fr_2eexists_5fstring_5flength => match i {
0 => Some(ArgKind::Type),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5feq_5fsingleton_5femp => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5fmember_5femp => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5finter_5femp1 => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5finter_5femp2 => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5fminus_5femp1 => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5fminus_5femp2 => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5funion_5femp1 => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5funion_5femp2 => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5fminus_5fself => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5fis_5fempty_5felim => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
3 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
3 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
3 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
3 => Some(ArgKind::Term),
4 => Some(ArgKind::Term),
5 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fconcat_5funify_5fbase => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
3 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
3 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fcontains_5fchar => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Term),
3 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5findexof_5fself => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::Term),
2 => Some(ArgKind::Type),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5fmember_5fsingleton => match i {
0 => Some(ArgKind::Term),
1 => Some(ArgKind::WfElem),
_ => None,
},
Constructor::eo__24emb_5fr_2esets_5fchoose_5fsingleton => match i {
0 => Some(ArgKind::WfElem),
_ => None,
},
Constructor::eo__24emb_5fr_2eseq_5flen_5funit => match i {
0 => Some(ArgKind::WfElem),
_ => None,
},
Constructor::eo__24emb_5fr_2eseq_5frev_5funit => match i {
0 => Some(ArgKind::WfElem),
_ => None,
},
Constructor::eo__24emb_5fr_2eseq_5fnth_5funit => match i {
0 => Some(ArgKind::WfElem),
_ => None,
},

            _ => None,
        }
    }

    fn translation_type(&mut self, t: Term) -> CheckResult<Term> {
        let t = generated::eo__24eo_5fto_5fsmt(self, t)?; generated::eo__24smtx_5ftypeof(self, t)
    }
    fn translation_sort(&mut self, t: Term) -> CheckResult<Term> {
        generated::eo__24eo_5fto_5fsmt_5ftype(self, t)
    }
    fn translation_type_wf(&mut self, t: Term, component: bool) -> CheckResult<bool> {
        let b = if component { generated::eo__24smtx_5ftype_5fwf_5fcomponent(self, t)? } else { generated::eo__24smtx_5ftype_5fwf(self, t)? }; self.is_native_true(b)
    }
    fn has_translation(&mut self, t: Term) -> CheckResult<bool> {
        let ty = self.translation_type(t)?;
        Ok(!self.is_stuck(ty)? && !self.is_node(ty, Some(Constructor::eo__24emb_5ftsm_2eNone))?)
    }
    fn argument_translates(&mut self, t: Term, which: ArgKind) -> CheckResult<bool> {
        match which {
            ArgKind::Term => self.has_translation(t),
            ArgKind::Type => {
                let ty = self.translation_sort(t)?;
                self.translation_type_wf(ty, false)
            }
            ArgKind::WfTerm => {
                if !self.has_translation(t)? {
                    return Ok(false);
                }
                let ty = self.translation_type(t)?;
                self.translation_type_wf(ty, false)
            }
            ArgKind::WfElem => {
                let ty = self.translation_type(t)?;
                self.translation_type_wf(ty, true)
            }
            ArgKind::List => {
                let mut list = t;
                loop {
                    if self.is_node(list, Some(Constructor::eo__24eo_5fList_5fnil))? {
                        return Ok(true);
                    }
                    let Some((fx, tail)) = self.unapply(list)? else {
                        return Ok(false);
                    };
                    let Some((f, x)) = self.unapply(fx)? else {
                        return Ok(false);
                    };
                    if !self.is_node(f, Some(Constructor::eo__24eo_5fList_5fcons))? || !self.has_translation(x)? {
                        return Ok(false);
                    }
                    list = tail;
                }
            }
            ArgKind::Unknown => Err(CheckError::InvalidConstructor),
        }
    }
    /// Whether the arguments translate: each as a term, or, for a rule
    /// with a mask, as its mask says.
    fn arguments_translate(
        &mut self,
        mut args: Term,
        rule: Option<Constructor>,
    ) -> CheckResult<bool> {
        let mask = match rule {
            Some(rule) => match Self::mask_len(rule) {
                Some(len) => Some((rule, len)),
                None => None,
            },
            None => None,
        };
        let mut i = 0;
        loop {
            if self.is_node(args, Some(Constructor::eo__24emb_5fal_2enil))? {
                return Ok(match mask {
                    Some((_, len)) => i == len,
                    None => true,
                });
            }
            let Some(fs) = self.node_fields(args, Some(Constructor::eo__24emb_5fal_2econs))? else {
                return Ok(false);
            };
            let which = match mask {
                Some((rule, _)) => match Self::mask_kind(rule, i) {
                    Some(k) => k,
                    None => return Ok(false),
                },
                None => ArgKind::Term,
            };
            if !self.argument_translates(fs[0], which)? {
                return Ok(false);
            }
            args = fs[1];
            i += 1;
        }
    }
}
