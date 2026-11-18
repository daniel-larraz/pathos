//! Generated functions, module 1 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn case_9_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_56_eo__24arith_5freduction_5fpred(s, v8, v12, v4, v2)
}
pub(super) fn cases_0_2_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_reduction_pred"
pub fn eo__24arith_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5freduction_5fpred(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_2_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_3_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn cases_0_0_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24arith_5frel_5finv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24arith_5frel_5finv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24arith_5frel_5finv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24arith_5frel_5finv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn cases_0_1_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24arith_5frel_5finv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24arith_5frel_5finv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24arith_5frel_5finv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_rel_inv"
pub fn eo__24arith_5frel_5finv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5frel_5finv(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_2_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_3_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_0_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_5_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_6_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_7_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_1_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_8_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_2_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_rel_sum"
pub fn eo__24arith_5frel_5fsum(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5frel_5fsum(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_2_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_3_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_0_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_5_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_1_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$arith_rel_trichotomy"
pub fn eo__24arith_5frel_5ftrichotomy(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24arith_5frel_5ftrichotomy(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24assoc_5fnil_5fnth(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v7 { return Ok(None); }
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_1_eo__24assoc_5fnil_5fnth(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Add, &[a2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, v2, v8])))
}
pub(super) fn step_eo__24assoc_5fnil_5fnth(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24assoc_5fnil_5fnth(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24assoc_5fnil_5fnth(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24assoc_5fnil_5fnth(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24assoc_5fnil_5fnth(s, a0, a1, a2) {
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
// EO program "$assoc_nil_nth"
pub fn eo__24assoc_5fnil_5fnth(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(14), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24assoc_5fnil_5fnth(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(14), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24assoc_5fnil_5fnth_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v7 { return Ok(None); }
let v8 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_1_eo__24assoc_5fnil_5fnth_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Add, &[a2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, v2, v8])))
}
pub(super) fn step_eo__24assoc_5fnil_5fnth_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24assoc_5fnil_5fnth_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24assoc_5fnil_5fnth_5ftype(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24assoc_5fnil_5fnth_5ftype(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24assoc_5fnil_5fnth_5ftype(s, a0, a1, a2) {
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
// EO program "$assoc_nil_nth_type"
pub fn eo__24assoc_5fnil_5fnth_5ftype(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(15), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24assoc_5fnil_5fnth_5ftype(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(15), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fapply_5fbinary(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v3 { return Ok(None); }
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Binary(BitVec::new(0, &v4))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn more_0_eo__24bv_5fbitblast_5fapply_5fbinary(s: &mut Store, v16: Term, v17: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fbinary_5fapp(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fbinary_5fapp(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_2_eo__24bv_5fbitblast_5fbinary_5fapp(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_3_eo__24bv_5fbitblast_5fbinary_5fapp(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24bv_5fbitblast_5fbinary_5fapp(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fbinary_5fapp(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fbinary_5fapp(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24bv_5fbitblast_5fbinary_5fapp(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24bv_5fbitblast_5fbinary_5fapp(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_bitblast_binary_app"
pub fn eo__24bv_5fbitblast_5fbinary_5fapp(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fbitblast_5fbinary_5fapp(s, a0, a1, a2);
s.leave();
result
}
// EO program "$bv_bitblast_apply_binary"
pub fn eo__24bv_5fbitblast_5fapply_5fbinary(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(16), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fbitblast_5fapply_5fbinary(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(16), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fbitblast_5fapply_5fbinary(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fapply_5fbinary(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fapply_5fbinary(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fapply_5fbinary(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24bv_5fbitblast_5fbinary_5fapp(s, a0, v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24bv_5fbitblast_5fapply_5fbinary(s, a0, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fbitblast_5fapply_5fbinary(s, v16, v17)
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fapply_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v3 { return Ok(None); }
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Binary(BitVec::new(0, &v4))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$bv_bitblast_apply_ite"
pub fn eo__24bv_5fbitblast_5fapply_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(17), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fbitblast_5fapply_5fite(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(17), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fbitblast_5fapply_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fapply_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fapply_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fapply_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fbitblast_5fapply_5fite(s, v17, v12, v14, a0, v2, v9)
}
pub(super) fn more_0_eo__24bv_5fbitblast_5fapply_5fite(s: &mut Store, v17: Term, v12: Term, v14: Term, a0: Term, v2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24bv_5fbitblast_5fapply_5fite(s, a0, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fapply_5funary(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$bv_bitblast_apply_unary"
pub fn eo__24bv_5fbitblast_5fapply_5funary(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(18), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fbitblast_5fapply_5funary(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(18), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fbitblast_5fapply_5funary(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fapply_5funary(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fapply_5funary(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fapply_5funary(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitblast_5fapply_5funary(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
Ok(Some(a1))
}
// EO program "$bv_bitblast_concat"
pub fn eo__24bv_5fbitblast_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(20), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fbitblast_5fconcat(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(20), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fbitblast_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fbitblast_5fconcat(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fhead(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
Ok(Some(v5))
}
pub(super) fn body_eo__24bv_5fbitblast_5fhead(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fhead(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_bitblast_head"
pub fn eo__24bv_5fbitblast_5fhead(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fbitblast_5fhead(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(v0)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$bv_bitblast_prefix"
pub fn eo__24bv_5fbitblast_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(22), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fbitblast_5fprefix(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(22), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fbitblast_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24bv_5fbitblast_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24bv_5fbitblast_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(v9)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Add, &[a0, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fbitblast_5fprefix(s, v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn more_0_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, v29: Term, v25: Term, v23: Term, v22: Term) -> CheckResult<Term> {
let v30 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v25, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v23, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v22, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
pub(super) fn if_1_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, condition: Term, v5: Term, v14: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fbitblast_5fslt_5fimpl(s, v29, v25, v23, v22)
}
Some(false) => {
let v37 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v42, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v38, v44) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, a2: Term, v5: Term, v14: Term) -> CheckResult<Option<Term>> {
let v46 = match if_1_eo__24bv_5fbitblast_5fslt_5fimpl(s, a2, v5, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v46))
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Binary(BitVec::new(0, &v7))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v8 { return Ok(None); }
let v9 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Binary(BitVec::new(0, &v16))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v17 { return Ok(None); }
more_2_eo__24bv_5fbitblast_5fslt_5fimpl(s, a2, v5, v14)
}
pub(super) fn more_5_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, v41: Term, v30: Term) -> CheckResult<Option<Term>> {
let v42 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v30, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v44))
}
pub(super) fn more_4_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, v14: Term, v29: Term, v5: Term, v12: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v14, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v37, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v33, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v31, v40) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24bv_5fbitblast_5fslt_5fimpl(s, v41, v30)
}
pub(super) fn more_0_eo__24bv_5fbitblast_5fult(s: &mut Store, v5: Term, v12: Term, v25: Term, v24: Term) -> CheckResult<Term> {
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v24, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn if_1_eo__24bv_5fbitblast_5fult(s: &mut Store, condition: Term, v5: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v14, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fbitblast_5fult(s, v5, v12, v25, v24)
}
Some(false) => {
let v33 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v36, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fult_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v3 { return Ok(None); }
Ok(Some(Next::Done(a2)))
}
pub(super) fn more_1_eo__24bv_5fbitblast_5fult_5frec(s: &mut Store, v27: Term, v29: Term, v12: Term, v26: Term, v25: Term, v2: Term, v9: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v30, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v26, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v25, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v9, v39])))
}
pub(super) fn more_0_eo__24bv_5fbitblast_5fult_5frec(s: &mut Store, v17: Term, v12: Term, v15: Term, a2: Term, v14: Term, v5: Term, v2: Term, v9: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v14, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fbitblast_5fult_5frec(s, v27, v29, v12, v26, v25, v2, v9)
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fult_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fbitblast_5fult_5frec(s, v17, v12, v15, a2, v14, v5, v2, v9)
}
pub(super) fn step_eo__24bv_5fbitblast_5fult_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fult_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fult_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fbitblast_5fult_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fbitblast_5fult_5frec(s, a0, a1, a2) {
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
// EO program "$bv_bitblast_ult_rec"
pub fn eo__24bv_5fbitblast_5fult_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(27), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fbitblast_5fult_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(27), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fult(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v42 = match if_1_eo__24bv_5fbitblast_5fult(s, a2, v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24bv_5fbitblast_5fult_5frec(s, v2, v9, v42) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v43))
}
pub(super) fn body_eo__24bv_5fbitblast_5fult(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fult(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_bitblast_ult"
pub fn eo__24bv_5fbitblast_5fult(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fbitblast_5fult(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn more_3_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, v17: Term, v12: Term, v15: Term, v2: Term, v9: Term, a2: Term, v14: Term, v5: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListRev, &[v21, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListRev, &[v23, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24bv_5fbitblast_5fult(s, v22, v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v20, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v19, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24bv_5fbitblast_5fslt_5fimpl(s, v14, v29, v5, v12)
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24bv_5fbitblast_5fslt_5fimpl(s, v17, v12, v15, v2, v9, a2, v14, v5)
}
pub(super) fn body_eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fslt_5fimpl(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fslt_5fimpl(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_bitblast_slt_impl"
pub fn eo__24bv_5fbitblast_5fslt_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fbitblast_5fslt_5fimpl(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24bv_5fbitblast_5fsubsequence(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_1_eo__24bv_5fbitblast_5fsubsequence(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(v0)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(v2)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::Add, &[a1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24bv_5fbitblast_5fprefix(s, v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_2_eo__24bv_5fbitblast_5fsubsequence(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[a0, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[a1, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v9, v12, v2])))
}
pub(super) fn step_eo__24bv_5fbitblast_5fsubsequence(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5fsubsequence(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fbitblast_5fsubsequence(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24bv_5fbitblast_5fsubsequence(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fbitblast_5fsubsequence(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fbitblast_5fsubsequence(s, a0, a1, a2) {
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
// EO program "$bv_bitblast_subsequence"
pub fn eo__24bv_5fbitblast_5fsubsequence(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(24), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fbitblast_5fsubsequence(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(24), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24bv_5fbitblast_5ftail(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24bv_5fbitblast_5ftail(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitblast_5ftail(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_bitblast_tail"
pub fn eo__24bv_5fbitblast_5ftail(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fbitblast_5ftail(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24bv_5fbitwidth(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24bv_5fbitwidth(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fbitwidth(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_bitwidth"
pub fn eo__24bv_5fbitwidth(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fbitwidth(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24bv_5fconst_5fto_5fbitlist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Binary(BitVec::new(0, &v5))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
// EO program "$bv_const_to_bitlist_rec"
pub fn eo__24bv_5fconst_5fto_5fbitlist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(29), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fconst_5fto_5fbitlist_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(29), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fconst_5fto_5fbitlist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fconst_5fto_5fbitlist_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fconst_5fto_5fbitlist_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fconst_5fto_5fbitlist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Extract, &[a0, v5, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Binary(BitVec::new(1, &v9))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Eq, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fconst_5fto_5fbitlist_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if a2 != a0 { return Ok(None); }
let v0 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn more_2_eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, v41: Term, v12: Term, v39: Term, a2: Term, v38: Term, a3: Term, v2: Term, v9: Term, v37: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v42 = match s.apply(v41, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v39, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v38, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v9, v37, v46])))
}
pub(super) fn more_1_eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, v29: Term, a2: Term, v28: Term, v23: Term, v22: Term, v5: Term, v12: Term, a3: Term, v2: Term, v9: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v30 = match s.apply(v29, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v30, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v28, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v23, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v22, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v41, v12, v39, a2, v38, a3, v2, v9, v37)
}
pub(super) fn more_0_eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, v17: Term, v12: Term, v16: Term, v14: Term, v5: Term, a2: Term, a3: Term, v2: Term, v9: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v16, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v29, a2, v28, v23, v22, v5, v12, a3, v2, v9)
}
pub(super) fn case_0_eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v17, v12, v16, v14, v5, a2, a3, v2, v9)
}
pub(super) fn case_1_eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListRev, &[v6, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn step_eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Next<[Term; 4]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fripple_5fcarry_5fadder_5f2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fripple_5fcarry_5fadder_5f2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fripple_5fcarry_5fadder_5f2(s, a0, a1, a2, a3) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
a3 = next[3];
}
Err(e) => return Err(e),
}
}
}
// EO program "$bv_ripple_carry_adder_2"
pub fn eo__24bv_5fripple_5fcarry_5fadder_5f2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(47), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fripple_5fcarry_5fadder_5f2(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(47), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24pair_5fsecond(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24pair_5fsecond(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24pair_5fsecond(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$pair_second"
pub fn eo__24pair_5fsecond(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24pair_5fsecond(s, a0);
s.leave();
result
}
pub(super) fn more_27_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v391: Term, v393: Term, v394: Term, v269: Term, v330: Term, v199: Term, a0: Term, v190: Term) -> CheckResult<Option<Term>> {
let v395 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.literal(Lit::Binary(BitVec::new(0, &v395))) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v391, v393, v394, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match eo__24pair_5fsecond(s, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match eo__24bv_5fbitblast_5fapply_5fite(s, v269, v330, v398) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match eo__24bv_5fbitblast_5fapply_5fite(s, v199, a0, v399) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.apply(v190, v400) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v401))
}
pub(super) fn more_26_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v380: Term, v381: Term, v377: Term, v376: Term, a2: Term, a1: Term, v269: Term, v330: Term, v199: Term, a0: Term, v190: Term) -> CheckResult<Option<Term>> {
let v382 = match s.apply(v380, v381) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.apply(v377, v382) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.apply(v383, v384) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.apply(v385, v386) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.literal(Lit::Binary(BitVec::new(0, &v388))) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v376, a2, v387, v389) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match eo__24pair_5fsecond(s, v390) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match eo__24bv_5fbitblast_5fapply_5funary(s, v392, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24bv_5fdiv_5fmod_5fimpl(s, v391, v393, v394, v269, v330, v199, a0, v190)
}
pub(super) fn case_0_eo__24pair_5ffirst(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
Ok(Some(v5))
}
pub(super) fn body_eo__24pair_5ffirst(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24pair_5ffirst(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$pair_first"
pub fn eo__24pair_5ffirst(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24pair_5ffirst(s, a0);
s.leave();
result
}
// EO program "$bv_div_mod_impl"
pub fn eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(30), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(30), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitblast_5fapply_5funary(s, v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Binary(BitVec::new(0, &v12))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, a0, v10, v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24pair_5ffirst(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fdiv_5fmod_5fimpl(s, v8, v15, a0, a1, a2, v2, v7)
}
pub(super) fn more_25_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v368: Term, v365: Term, a1: Term, a2: Term, v2: Term, v338: Term, v360: Term, v336: Term, a0: Term, v269: Term, v330: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v369 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.literal(Lit::Binary(BitVec::new(0, &v369))) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.apply(v368, v370) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match eo__24bv_5fbitblast_5fconcat(s, v365, v371) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v372, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match eo__24pair_5fsecond(s, v373) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match eo__24bv_5fbitblast_5fsubsequence(s, v338, v360, v374) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match eo__24bv_5fbitblast_5fconcat(s, v336, v375) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match eo__24bv_5fbitblast_5fhead(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.apply(v378, v379) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24bv_5fdiv_5fmod_5fimpl(s, v380, v381, v377, v376, a2, a1, v269, v330, v199, a0, v190)
}
pub(super) fn more_24_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v339: Term, v353: Term, a0: Term, a1: Term, a2: Term, v2: Term, v338: Term, v336: Term, v269: Term, v330: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v354 = match s.builtin_list(EvalOp::ListLength, &[v339, v353]) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.literal(Lit::Numeral(v355)) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.builtin_core(EvalOp::Add, &[v354, v356]) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.literal(Lit::Numeral(v358)) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.builtin_core(EvalOp::Add, &[v357, v359]) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.literal(Lit::Numeral(v361)) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.builtin_list(EvalOp::ListLength, &[v363, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match eo__24bv_5fbitblast_5fsubsequence(s, v362, v364, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.apply(v366, v367) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24bv_5fdiv_5fmod_5fimpl(s, v368, v365, a1, a2, v2, v338, v360, v336, a0, v269, v330, v199, v190)
}
pub(super) fn more_23_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, a1: Term, a2: Term, v2: Term, v339: Term, v338: Term, v336: Term, v269: Term, v330: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v340 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.literal(Lit::Numeral(v340)) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.builtin_list(EvalOp::ListLength, &[v342, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match eo__24bv_5fbitblast_5fsubsequence(s, v341, v343, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v345, v346) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.literal(Lit::Binary(BitVec::new(0, &v348))) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.apply(v347, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match eo__24bv_5fbitblast_5fconcat(s, v344, v350) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v351, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match eo__24pair_5fsecond(s, v352) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24bv_5fdiv_5fmod_5fimpl(s, v339, v353, a0, a1, a2, v2, v338, v336, v269, v330, v199, v190)
}
pub(super) fn more_22_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v324: Term, v315: Term, a2: Term, a0: Term, a1: Term, v2: Term, v269: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v325 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v324, v325) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.literal(Lit::Binary(BitVec::new(0, &v327))) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v315, a2, v326, v328) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match eo__24pair_5fsecond(s, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v331, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.literal(Lit::Binary(BitVec::new(0, &v334))) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v333, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.literal(Lit::Numeral(v337)) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, a1, a2, v2, v339, v338, v336, v269, v330, v199, v190)
}
pub(super) fn more_21_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v312: Term, v277: Term, v299: Term, v275: Term, a0: Term, a2: Term, a1: Term, v2: Term, v269: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v313 = match eo__24pair_5fsecond(s, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match eo__24bv_5fbitblast_5fsubsequence(s, v277, v299, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match eo__24bv_5fbitblast_5fconcat(s, v275, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match eo__24bv_5fbitblast_5fhead(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v317, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v319, v320) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v316, v321) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v322, v323) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24bv_5fdiv_5fmod_5fimpl(s, v324, v315, a2, a0, a1, v2, v269, v199, v190)
}
pub(super) fn more_20_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v296: Term, v298: Term, a0: Term, a1: Term, a2: Term, v2: Term, v277: Term, v275: Term, v269: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v299 = match s.builtin_core(EvalOp::Add, &[v296, v298]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.literal(Lit::Numeral(v300)) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.builtin_list(EvalOp::ListLength, &[v302, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match eo__24bv_5fbitblast_5fsubsequence(s, v301, v303, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v305, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.literal(Lit::Binary(BitVec::new(0, &v308))) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v307, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match eo__24bv_5fbitblast_5fconcat(s, v304, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v311, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24bv_5fdiv_5fmod_5fimpl(s, v312, v277, v299, v275, a0, a2, a1, v2, v269, v199, v190)
}
pub(super) fn more_19_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v283: Term, a1: Term, a2: Term, v2: Term, v278: Term, a0: Term, v277: Term, v275: Term, v269: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v284 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v284, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.literal(Lit::Binary(BitVec::new(0, &v287))) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.apply(v286, v288) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match eo__24bv_5fbitblast_5fconcat(s, v283, v289) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v290, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match eo__24pair_5fsecond(s, v291) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.builtin_list(EvalOp::ListLength, &[v278, v292]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.literal(Lit::Numeral(v294)) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.builtin_core(EvalOp::Add, &[v293, v295]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.literal(Lit::Numeral(v297)) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24bv_5fdiv_5fmod_5fimpl(s, v296, v298, a0, a1, a2, v2, v277, v275, v269, v199, v190)
}
pub(super) fn more_18_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v200: Term, v268: Term, a0: Term, a1: Term, a2: Term, v2: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v269 = match s.apply(v200, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v270, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.literal(Lit::Binary(BitVec::new(0, &v273))) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v272, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.literal(Lit::Numeral(v276)) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.literal(Lit::Numeral(v279)) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.builtin_list(EvalOp::ListLength, &[v281, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match eo__24bv_5fbitblast_5fsubsequence(s, v280, v282, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24bv_5fdiv_5fmod_5fimpl(s, v283, a1, a2, v2, v278, a0, v277, v275, v269, v199, v190)
}
pub(super) fn more_17_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v253: Term, v254: Term, v246: Term, a2: Term, a1: Term, v200: Term, a0: Term, v2: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v255 = match s.apply(v253, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v255, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.literal(Lit::Binary(BitVec::new(0, &v258))) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v246, a2, v257, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match eo__24pair_5fsecond(s, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match eo__24bv_5fbitblast_5fapply_5funary(s, v262, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Binary(BitVec::new(0, &v265))) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v261, v263, v264, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match eo__24pair_5ffirst(s, v267) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24bv_5fdiv_5fmod_5fimpl(s, v200, v268, a0, a1, a2, v2, v199, v190)
}
pub(super) fn more_16_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v242: Term, a1: Term, a2: Term, v2: Term, v208: Term, v230: Term, v206: Term, a0: Term, v200: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v243 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v242, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match eo__24pair_5fsecond(s, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match eo__24bv_5fbitblast_5fsubsequence(s, v208, v230, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match eo__24bv_5fbitblast_5fconcat(s, v206, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match eo__24bv_5fbitblast_5fhead(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v248, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v250, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v247, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24bv_5fdiv_5fmod_5fimpl(s, v253, v254, v246, a2, a1, v200, a0, v2, v199, v190)
}
pub(super) fn more_15_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v227: Term, a0: Term, a1: Term, a2: Term, v2: Term, v208: Term, v206: Term, v200: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v228 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.literal(Lit::Numeral(v228)) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.builtin_core(EvalOp::Add, &[v227, v229]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.literal(Lit::Numeral(v231)) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.builtin_list(EvalOp::ListLength, &[v233, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match eo__24bv_5fbitblast_5fsubsequence(s, v232, v234, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v236, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.literal(Lit::Binary(BitVec::new(0, &v239))) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v238, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match eo__24bv_5fbitblast_5fconcat(s, v235, v241) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24bv_5fdiv_5fmod_5fimpl(s, v242, a1, a2, v2, v208, v230, v206, a0, v200, v199, v190)
}
pub(super) fn more_14_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v211: Term, v213: Term, a0: Term, a1: Term, a2: Term, v2: Term, v209: Term, v208: Term, v206: Term, v200: Term, v199: Term, v190: Term) -> CheckResult<Option<Term>> {
let v214 = match eo__24bv_5fbitblast_5fsubsequence(s, v211, v213, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v215, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.literal(Lit::Binary(BitVec::new(0, &v218))) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v217, v219) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match eo__24bv_5fbitblast_5fconcat(s, v214, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v221, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match eo__24pair_5fsecond(s, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.builtin_list(EvalOp::ListLength, &[v209, v223]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.literal(Lit::Numeral(v225)) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_core(EvalOp::Add, &[v224, v226]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24bv_5fdiv_5fmod_5fimpl(s, v227, a0, a1, a2, v2, v208, v206, v200, v199, v190)
}
pub(super) fn more_13_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v191: Term, v198: Term, a0: Term, a1: Term, a2: Term, v2: Term, v190: Term) -> CheckResult<Option<Term>> {
let v199 = match s.apply(v191, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v201, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.literal(Lit::Binary(BitVec::new(0, &v204))) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v203, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.literal(Lit::Numeral(v207)) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.literal(Lit::Numeral(v210)) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_list(EvalOp::ListLength, &[v212, a0]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24bv_5fdiv_5fmod_5fimpl(s, v211, v213, a0, a1, a2, v2, v209, v208, v206, v200, v199, v190)
}
pub(super) fn more_12_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v146: Term, v185: Term, v140: Term, v16: Term, a2: Term, v7: Term, a1: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
let v186 = match eo__24bv_5fbitblast_5fconcat(s, v146, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match eo__24bv_5fbitblast_5ftail(s, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v140, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match eo__24bv_5fbitblast_5fapply_5fite(s, v16, a2, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v7, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24bv_5fbitblast_5fapply_5funary(s, v192, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.literal(Lit::Binary(BitVec::new(0, &v195))) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, a0, v193, v194, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match eo__24pair_5ffirst(s, v197) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24bv_5fdiv_5fmod_5fimpl(s, v191, v198, a0, a1, a2, v2, v190)
}
pub(super) fn more_11_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, v172: Term, a1: Term, a2: Term, v2: Term, v148: Term, v170: Term, v146: Term, v140: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v173 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.builtin_list(EvalOp::ListLength, &[v173, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match eo__24bv_5fbitblast_5fsubsequence(s, v172, v174, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v176, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.literal(Lit::Binary(BitVec::new(0, &v179))) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v178, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match eo__24bv_5fbitblast_5fconcat(s, v175, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v182, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match eo__24pair_5ffirst(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match eo__24bv_5fbitblast_5fsubsequence(s, v148, v170, v184) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24bv_5fdiv_5fmod_5fimpl(s, v146, v185, v140, v16, a2, v7, a1, a0, v2)
}
pub(super) fn more_10_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v155: Term, v156: Term, v154: Term, a1: Term, a2: Term, v2: Term, v149: Term, a0: Term, v148: Term, v146: Term, v140: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v157 = match s.apply(v155, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.literal(Lit::Binary(BitVec::new(0, &v158))) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v157, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match eo__24bv_5fbitblast_5fconcat(s, v154, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v161, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match eo__24pair_5ffirst(s, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.builtin_list(EvalOp::ListLength, &[v149, v163]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Numeral(v165)) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.builtin_core(EvalOp::Add, &[v164, v166]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.literal(Lit::Numeral(v168)) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.builtin_core(EvalOp::Add, &[v167, v169]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.literal(Lit::Numeral(v171)) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, v172, a1, a2, v2, v148, v170, v146, v140, v16, v7)
}
pub(super) fn more_9_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v141: Term, a0: Term, a1: Term, a2: Term, v2: Term, v140: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v142 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v141, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.literal(Lit::Binary(BitVec::new(0, &v144))) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v143, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Numeral(v147)) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Numeral(v150)) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.builtin_list(EvalOp::ListLength, &[v152, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match eo__24bv_5fbitblast_5fsubsequence(s, v151, v153, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24bv_5fdiv_5fmod_5fimpl(s, v155, v156, v154, a1, a2, v2, v149, a0, v148, v146, v140, v16, v7)
}
pub(super) fn more_8_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v127: Term, v129: Term, v124: Term, a1: Term, a2: Term, v2: Term, v97: Term, v119: Term, v95: Term, v89: Term, v17: Term, a0: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v130 = match s.apply(v127, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match eo__24bv_5fbitblast_5fconcat(s, v124, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v131, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match eo__24pair_5ffirst(s, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match eo__24bv_5fbitblast_5fsubsequence(s, v97, v119, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match eo__24bv_5fbitblast_5fconcat(s, v95, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24bv_5fbitblast_5fhead(s, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v89, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v137, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v17, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24bv_5fdiv_5fmod_5fimpl(s, v141, a0, a1, a2, v2, v140, v16, v7)
}
pub(super) fn more_7_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v113: Term, a0: Term, a1: Term, a2: Term, v2: Term, v97: Term, v95: Term, v89: Term, v17: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v114 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.literal(Lit::Numeral(v114)) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.builtin_core(EvalOp::Add, &[v113, v115]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(v117)) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.builtin_core(EvalOp::Add, &[v116, v118]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.literal(Lit::Numeral(v120)) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_list(EvalOp::ListLength, &[v122, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match eo__24bv_5fbitblast_5fsubsequence(s, v121, v123, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v125, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Binary(BitVec::new(0, &v128))) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24bv_5fdiv_5fmod_5fimpl(s, v127, v129, v124, a1, a2, v2, v97, v119, v95, v89, v17, a0, v16, v7)
}
pub(super) fn more_6_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, v100: Term, a1: Term, a2: Term, v2: Term, v98: Term, v97: Term, v95: Term, v89: Term, v17: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v101 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_list(EvalOp::ListLength, &[v101, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match eo__24bv_5fbitblast_5fsubsequence(s, v100, v102, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v104, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.literal(Lit::Binary(BitVec::new(0, &v107))) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v106, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match eo__24bv_5fbitblast_5fconcat(s, v103, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v110, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24pair_5ffirst(s, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.builtin_list(EvalOp::ListLength, &[v98, v112]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24bv_5fdiv_5fmod_5fimpl(s, v113, a0, a1, a2, v2, v97, v95, v89, v17, v16, v7)
}
pub(super) fn more_5_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v80: Term, v82: Term, v83: Term, v85: Term, v19: Term, v18: Term, a0: Term, a1: Term, a2: Term, v2: Term, v17: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v86 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v80, v82, v83, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24pair_5ffirst(s, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v19, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v18, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v90, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Binary(BitVec::new(0, &v93))) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Numeral(v96)) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(v99)) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, v100, a1, a2, v2, v98, v97, v95, v89, v17, v16, v7)
}
pub(super) fn more_4_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v66: Term, v71: Term, v65: Term, a2: Term, a1: Term, v19: Term, v18: Term, a0: Term, v2: Term, v17: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v72 = match s.apply(v66, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v72, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v74, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Binary(BitVec::new(0, &v77))) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v65, a2, v76, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match eo__24pair_5fsecond(s, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match eo__24bv_5fbitblast_5fapply_5funary(s, v81, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Binary(BitVec::new(0, &v84))) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24bv_5fdiv_5fmod_5fimpl(s, v80, v82, v83, v85, v19, v18, a0, a1, a2, v2, v17, v16, v7)
}
pub(super) fn more_3_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v57: Term, v59: Term, v54: Term, a1: Term, a2: Term, v2: Term, v27: Term, v49: Term, v25: Term, a0: Term, v19: Term, v18: Term, v17: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v60 = match s.apply(v57, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24bv_5fbitblast_5fconcat(s, v54, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v61, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24pair_5fsecond(s, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24bv_5fbitblast_5fsubsequence(s, v27, v49, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24bv_5fbitblast_5fconcat(s, v25, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24bv_5fbitblast_5fhead(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v69, v70) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24bv_5fdiv_5fmod_5fimpl(s, v66, v71, v65, a2, a1, v19, v18, a0, v2, v17, v16, v7)
}
pub(super) fn more_2_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v43: Term, a0: Term, a1: Term, a2: Term, v2: Term, v27: Term, v25: Term, v19: Term, v18: Term, v17: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v44 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(v44)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_core(EvalOp::Add, &[v43, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::Add, &[v46, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Numeral(v50)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_list(EvalOp::ListLength, &[v52, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24bv_5fbitblast_5fsubsequence(s, v51, v53, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v55, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Binary(BitVec::new(0, &v58))) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24bv_5fdiv_5fmod_5fimpl(s, v57, v59, v54, a1, a2, v2, v27, v49, v25, a0, v19, v18, v17, v16, v7)
}
pub(super) fn more_1_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, a0: Term, v30: Term, a1: Term, a2: Term, v2: Term, v28: Term, v27: Term, v25: Term, v19: Term, v18: Term, v17: Term, v16: Term, v7: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_list(EvalOp::ListLength, &[v31, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24bv_5fbitblast_5fsubsequence(s, v30, v32, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Binary(BitVec::new(0, &v37))) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24bv_5fbitblast_5fconcat(s, v33, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v40, a1, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24pair_5fsecond(s, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListLength, &[v28, v42]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fdiv_5fmod_5fimpl(s, v43, a0, a1, a2, v2, v27, v25, v19, v18, v17, v16, v7)
}
pub(super) fn more_0_eo__24bv_5fdiv_5fmod_5fimpl(s: &mut Store, v8: Term, v15: Term, a0: Term, a1: Term, a2: Term, v2: Term, v7: Term) -> CheckResult<Option<Term>> {
let v16 = match s.apply(v8, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Binary(BitVec::new(0, &v23))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(v26)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(v29)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fdiv_5fmod_5fimpl(s, a0, v30, a1, a2, v2, v28, v27, v25, v19, v18, v17, v16, v7)
}
pub(super) fn case_1_eo__24bv_5feval_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$bv_eval_concat"
pub fn eo__24bv_5feval_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(31), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5feval_5fconcat(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(31), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5feval_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5feval_5fconcat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5feval_5fconcat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24bv_5feval_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24bv_5feval_5fconcat(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Concat, &[v5, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
// EO program "$bv_get_first_const_child"
pub fn eo__24bv_5fget_5ffirst_5fconst_5fchild(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(32), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fget_5ffirst_5fconst_5fchild(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(32), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fget_5ffirst_5fconst_5fchild(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fget_5ffirst_5fconst_5fchild(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24bv_5fget_5ffirst_5fconst_5fchild(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.builtin_core(EvalOp::IsBin, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v6, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn if_0_eo__24bv_5fget_5ffirst_5fconst_5fchild(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v5)
}
Some(false) => {
let v7 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24bv_5fbitblast_5fapply_5funary(s, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$bv_mk_bitblast_step_eq_rec"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(37), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(37), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, v14, v17, v2, v9)
}
pub(super) fn more_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s: &mut Store, v14: Term, v17: Term, v2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListSingletonElim, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_2_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitblast_5fult(s, v5, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_3_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitblast_5fult(s, v5, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_0_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListRev, &[v7, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListRev, &[v9, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fbitblast_5fslt_5fimpl(s, v8, v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_5_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListRev, &[v7, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListRev, &[v9, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fbitblast_5fslt_5fimpl(s, v8, v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_6_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_extract, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match eo__24bv_5fbitblast_5fsubsequence(s, v5, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$bv_mk_bitblast_step_concat"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(36), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(36), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitblast_5fconcat(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_7_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24bv_5fmk_5fbitblast_5fstep_5fconcat(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn cases_0_1_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match eo__24bv_5fbitblast_5fapply_5fbinary(s, a1, a3, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, a1, v2, v6])))
}
pub(super) fn requires_0_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s: &mut Store, a2: Term, v1: Term, a3: Term) -> CheckResult<Term> {
if a2 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a3)
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match eo__24eo_5ftypeof(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5fnil(s, a0, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match requires_0_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, a2, v1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn step_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Next<[Term; 4]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, a0, a1, a2, a3) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
a3 = next[3];
}
Err(e) => return Err(e),
}
}
}
// EO program "$bv_mk_bitblast_step_bitwise"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(35), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(35), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_8_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, v7, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_9_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, v7, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_10_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fmk_5fbitblast_5fstep_5fbitwise(s, v7, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_11_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvxnor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitblast_5fapply_5fbinary(s, v7, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_2_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Binary(BitVec::new(0, &v8))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, a1, v5, v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24pair_5fsecond(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v11])))
}
pub(super) fn requires_0_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s: &mut Store, v0: Term, v2: Term, a1: Term) -> CheckResult<Term> {
if v0 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a1)
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(v1)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match requires_0_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s, v0, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn step_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$bv_mk_bitblast_step_add"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(34), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(34), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_12_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24bv_5fmk_5fbitblast_5fstep_5fadd(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
Ok(Some(Next::Done(a3)))
}
pub(super) fn case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(v0)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v3 { return Ok(None); }
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Binary(BitVec::new(0, &v4))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$bv_shift_add_multiplier_rec_step"
pub fn eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(50), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(50), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v8 { return Ok(None); }
let v9 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, v14, a0, v5, v17, a4, v16, v2, v11)
}
pub(super) fn case_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(v9)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Add, &[a2, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, a0, a1, v11, v2, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn more_4_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, v49: Term, v66: Term, v48: Term, a0: Term, v2: Term, v32: Term, v11: Term, v30: Term) -> CheckResult<Option<Term>> {
let v67 = match s.apply(v49, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v48, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, a0, v2, v32, v11, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v30, v71) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v72))
}
pub(super) fn more_3_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, v5: Term, v54: Term, v52: Term, v50: Term, a4: Term, v49: Term, v48: Term, a0: Term, v2: Term, v32: Term, v11: Term, v30: Term) -> CheckResult<Option<Term>> {
let v55 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v56, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v54, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v52, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v50, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v63, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v61, v65) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, v49, v66, v48, a0, v2, v32, v11, v30)
}
pub(super) fn more_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, v38: Term, v42: Term, v36: Term, v35: Term, v33: Term, v14: Term, a0: Term, v5: Term, a4: Term, v2: Term, v32: Term, v11: Term, v30: Term) -> CheckResult<Option<Term>> {
let v43 = match s.apply(v38, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v36, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v35, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v33, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, v5, v54, v52, v50, a4, v49, v48, a0, v2, v32, v11, v30)
}
pub(super) fn more_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, v16: Term, v29: Term, v14: Term, a0: Term, v5: Term, a4: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v16, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(v31)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, v38, v42, v36, v35, v33, v14, a0, v5, a4, v2, v32, v11, v30)
}
pub(super) fn more_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s: &mut Store, v14: Term, a0: Term, v5: Term, v17: Term, a4: Term, v16: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v18 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v17, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, v16, v29, v14, a0, v5, a4, v2, v11)
}
pub(super) fn case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[a2, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep(s, v5, a1, a2, a3, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, a1, v9, v11])))
}
pub(super) fn step_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Next<[Term; 4]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s, a0, a1, a2, a3) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
a3 = next[3];
}
Err(e) => return Err(e),
}
}
}
// EO program "$bv_shift_add_multiplier_rec"
pub fn eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(49), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(49), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24bv_5fshift_5fadd_5fmultiplier(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fbitwidth(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListRepeat, &[v10, v5, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24bv_5fbitblast_5fapply_5fbinary(s, v9, v13, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24bv_5fshift_5fadd_5fmultiplier_5frec(s, v2, a0, v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn body_eo__24bv_5fshift_5fadd_5fmultiplier(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fshift_5fadd_5fmultiplier(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_shift_add_multiplier"
pub fn eo__24bv_5fshift_5fadd_5fmultiplier(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fshift_5fadd_5fmultiplier(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24bv_5fshift_5fadd_5fmultiplier(s, a1, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v7])))
}
pub(super) fn requires_0_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s: &mut Store, v0: Term, v2: Term, a1: Term) -> CheckResult<Term> {
if v0 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a1)
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(v1)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match requires_0_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s, v0, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn step_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$bv_mk_bitblast_step_mul"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(39), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(39), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_13_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24bv_5fmk_5fbitblast_5fstep_5fmul(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_0_eo__24iota_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
// EO program "$iota_rec"
pub fn eo__24iota_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(887), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24iota_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(887), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24iota_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24iota_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24iota_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24iota_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[a1, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24iota_5frec(s, v2, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn requires_0_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v27: Term, v28: Term, v5: Term) -> CheckResult<Term> {
if v27 != v28 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v27) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v29 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24bv_5fbitwidth(s, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListRepeat, &[v29, v31, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(v35)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24iota_5frec(s, v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v37)
}
pub(super) fn more_2_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v26: Term, v5: Term, v2: Term, v24: Term, v14: Term, v19: Term) -> CheckResult<Option<Term>> {
let v27 = match s.builtin_core(EvalOp::IsNeg, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match requires_0_eo__24bv_5fmk_5fbitblast_5fstep(s, v27, v28, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v5, v2, v24, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24pair_5ffirst(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24bv_5fbitblast_5fapply_5fite(s, v14, v19, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_1_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v5: Term, v2: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fbitwidth(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListRepeat, &[v15, v16, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24bv_5fbitwidth(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListRepeat, &[v20, v21, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24bv_5fbitwidth(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fmk_5fbitblast_5fstep(s, v26, v5, v2, v24, v14, v19)
}
pub(super) fn case_14_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24bv_5fbitwidth(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListRepeat, &[v8, v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSingletonElim, &[v7, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fmk_5fbitblast_5fstep(s, v5, v2, v14)
}
pub(super) fn requires_3_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v22: Term, v23: Term, v5: Term) -> CheckResult<Term> {
if v22 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24bv_5fbitwidth(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListRepeat, &[v24, v26, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24iota_5frec(s, v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn more_5_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v14: Term, v5: Term, v35: Term) -> CheckResult<Option<Term>> {
let v36 = match eo__24bv_5fbitblast_5fapply_5fite(s, v14, v5, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v36))
}
pub(super) fn more_4_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v5: Term, v2: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fbitwidth(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListRepeat, &[v15, v16, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24bv_5fbitwidth(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsNeg, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_3_eo__24bv_5fmk_5fbitblast_5fstep(s, v22, v23, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24bv_5fdiv_5fmod_5fimpl(s, v5, v2, v19, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24pair_5fsecond(s, v34) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24bv_5fmk_5fbitblast_5fstep(s, v14, v5, v35)
}
pub(super) fn case_15_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24bv_5fbitwidth(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListRepeat, &[v8, v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSingletonElim, &[v7, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24bv_5fmk_5fbitblast_5fstep(s, v5, v2, v14)
}
pub(super) fn cases_0_3_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_16_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitblast_5fapply_5funary(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Binary(BitVec::new(0, &v10))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v5, v8, v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24pair_5fsecond(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn more_6_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v5: Term, v10: Term, v11: Term, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match eo__24bv_5fripple_5fcarry_5fadder_5f2(s, v5, v10, v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24pair_5fsecond(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_17_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24bv_5fbitblast_5fapply_5funary(s, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fbitwidth(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListRepeat, &[v6, v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Binary(BitVec::new(0, &v12))) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24bv_5fmk_5fbitblast_5fstep(s, v5, v10, v11, v13)
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Binary(BitVec::new(0, &v7))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v8 { return Ok(None); }
let v9 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Binary(BitVec::new(0, &v9))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v10 { return Ok(None); }
let v11 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Binary(BitVec::new(0, &v11))) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v12 { return Ok(None); }
let v13 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Binary(BitVec::new(0, &v13))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
// EO program "$bv_mk_bitblast_step_ite"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(38), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(38), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Binary(BitVec::new(0, &v7))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v8 { return Ok(None); }
let v9 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, v20, v5, v14, v21, v11, v18)
}
pub(super) fn more_2_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s: &mut Store, v43: Term, v44: Term, v34: Term, v23: Term, v5: Term, v11: Term, v18: Term) -> CheckResult<Option<Term>> {
let v45 = match s.apply(v43, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v34, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v23, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Binary(BitVec::new(0, &v50))) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, v52, v11, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v47, v53) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v54))
}
pub(super) fn more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s: &mut Store, v28: Term, v32: Term, v24: Term, v5: Term, v21: Term, v23: Term, v11: Term, v18: Term) -> CheckResult<Option<Term>> {
let v33 = match s.apply(v28, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v24, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v37, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v35, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, v43, v44, v34, v23, v5, v11, v18)
}
pub(super) fn more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s: &mut Store, v20: Term, v5: Term, v14: Term, v21: Term, v11: Term, v18: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v30, v31) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, v28, v32, v24, v5, v21, v23, v11, v18)
}
pub(super) fn case_18_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24bv_5fmk_5fbitblast_5fstep_5fite(s, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn requires_7_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v18: Term, v19: Term, v5: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24bv_5fbitwidth(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24bv_5fbitwidth(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::ToBin, &[v24, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Length, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListRepeat, &[v20, v22, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24iota_5frec(s, v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn if_8_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v56 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Numeral(v56)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
Some(false) => {
let v58 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(v58)) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24bv_5fbitwidth(s, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.builtin_core(EvalOp::Log, &[v59, v61]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v53 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24bv_5fbitwidth(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_core(EvalOp::IsNeg, &[v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match if_8_eo__24bv_5fmk_5fbitblast_5fstep(s, v55, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v63)
}
Some(false) => {
let v64 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24bv_5fbitwidth(s, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v67)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v45 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
Some(false) => {
let v46 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24bv_5fbitwidth(s, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(v48)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24bv_5fbitwidth(s, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_core(EvalOp::IsZ, &[v51]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match if_9_eo__24bv_5fmk_5fbitblast_5fstep(s, v52, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::Pow, &[v49, v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_core(EvalOp::Eq, &[v47, v69]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v42 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24bv_5fbitwidth(s, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_core(EvalOp::IsNeg, &[v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match if_10_eo__24bv_5fmk_5fbitblast_5fstep(s, v44, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v71)
}
Some(false) => {
let v72 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24bv_5fbitwidth(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v72, v74) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v75)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_12_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v83 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(v83)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v84)
}
Some(false) => {
let v85 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(v85)) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match eo__24bv_5fbitwidth(s, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_core(EvalOp::Log, &[v86, v88]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v89)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_13_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v80 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match eo__24bv_5fbitwidth(s, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::IsNeg, &[v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match if_12_eo__24bv_5fmk_5fbitblast_5fstep(s, v82, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v90)
}
Some(false) => {
let v91 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24bv_5fbitwidth(s, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v91, v93) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v94)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v103)
}
Some(false) => {
let v104 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.literal(Lit::Numeral(v104)) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24bv_5fbitwidth(s, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_core(EvalOp::Log, &[v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v108)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v99 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match eo__24bv_5fbitwidth(s, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.builtin_core(EvalOp::IsNeg, &[v100]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match if_14_eo__24bv_5fmk_5fbitblast_5fstep(s, v101, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v109)
}
Some(false) => {
let v110 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24bv_5fbitwidth(s, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v110, v112) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v113)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v77 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match eo__24bv_5fbitwidth(s, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_core(EvalOp::IsZ, &[v78]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match if_13_eo__24bv_5fmk_5fbitblast_5fstep(s, v79, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v95)
}
Some(false) => {
let v96 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match eo__24bv_5fbitwidth(s, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.builtin_core(EvalOp::IsZ, &[v97]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match if_15_eo__24bv_5fmk_5fbitblast_5fstep(s, v98, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(v115)) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.builtin_core(EvalOp::Add, &[v114, v116]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v117)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_19_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v127: Term, v123: Term, v126: Term, v36: Term, v122: Term) -> CheckResult<Option<Term>> {
let v128 = match eo__24bv_5fbitwidth(s, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.builtin_list(EvalOp::ListRepeat, &[v123, v126, v128]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match eo__24bv_5fbitblast_5fapply_5fite(s, v36, v122, v129) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v130))
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
if a3 != a2 { return Ok(None); }
Ok(Some(Next::Done(a0)))
}
pub(super) fn if_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(v9)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Pow, &[v12, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.builtin_core(EvalOp::IsNeg, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_3_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[a2, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, v2, v9, a3, a4])))
}
// EO program "$bv_mk_bitblast_step_shr_rec_step"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(43), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(43), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a0, a1, a2, a3, a4) {
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
pub(super) fn step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Next<[Term; 5]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
let stuck4 = match s.is_stuck(a4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck4 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v15 { return Ok(None); }
let v16 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a3, v17, v5, v12, v16, v2, v9, a4)
}
pub(super) fn case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Binary(BitVec::new(0, &v7))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v8 { return Ok(None); }
let v9 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(v9)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, v14, v5, v11, v2, a3, a4)
}
pub(super) fn more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, a3: Term, v17: Term, v5: Term, v12: Term, v16: Term, v2: Term, v9: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v18 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(v24)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, v2, v9, v25, a3, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v27)))
}
pub(super) fn more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s: &mut Store, v14: Term, v5: Term, v11: Term, v2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Binary(BitVec::new(0, &v17))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, v2, v18, v20, a3, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v16, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v22)))
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsZ, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep(s, a0, a0, v17, v5, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Add, &[a2, v20]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v18, v2, v21, a3, a4])))
}
pub(super) fn step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Next<[Term; 5]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
let stuck4 = match s.is_stuck(a4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck4 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, a0, a1, a2, a3, a4) {
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
// EO program "$bv_mk_bitblast_step_shr_rec"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(42), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(42), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn more_18_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v40: Term, v5: Term, v2: Term, v38: Term, v36: Term) -> CheckResult<Option<Term>> {
let v41 = match s.builtin_core(EvalOp::IsZ, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match if_11_eo__24bv_5fmk_5fbitblast_5fstep(s, v41, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match if_16_eo__24bv_5fmk_5fbitblast_5fstep(s, v76, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.builtin_list(EvalOp::ListRev, &[v119, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match eo__24bv_5fbitblast_5fhead(s, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, v5, v2, v38, v118, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.builtin_list(EvalOp::ListRev, &[v124, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24bv_5fbitblast_5fhead(s, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24bv_5fmk_5fbitblast_5fstep(s, v127, v123, v126, v36, v122)
}
pub(super) fn more_17_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v14: Term, v13: Term, v5: Term, v11: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::ToBin, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Length, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_7_eo__24bv_5fmk_5fbitblast_5fstep(s, v18, v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24bv_5fconst_5fto_5fbitlist_5frec(s, v11, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24bv_5fbitblast_5fult(s, v2, v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24bv_5fbitwidth(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24bv_5fmk_5fbitblast_5fstep(s, v40, v5, v2, v38, v36)
}
pub(super) fn case_19_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::ToBin, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24bv_5fmk_5fbitblast_5fstep(s, v14, v13, v5, v11, v2)
}
pub(super) fn cases_0_4_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_20_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v18: Term, v19: Term, v5: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24bv_5fbitwidth(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24bv_5fbitwidth(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::ToBin, &[v24, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Length, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListRepeat, &[v20, v22, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24iota_5frec(s, v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn if_21_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v56 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Numeral(v56)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
Some(false) => {
let v58 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(v58)) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24bv_5fbitwidth(s, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.builtin_core(EvalOp::Log, &[v59, v61]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_22_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v53 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24bv_5fbitwidth(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_core(EvalOp::IsNeg, &[v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match if_21_eo__24bv_5fmk_5fbitblast_5fstep(s, v55, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v63)
}
Some(false) => {
let v64 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24bv_5fbitwidth(s, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v67)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_23_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v45 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
Some(false) => {
let v46 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24bv_5fbitwidth(s, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(v48)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24bv_5fbitwidth(s, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_core(EvalOp::IsZ, &[v51]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match if_22_eo__24bv_5fmk_5fbitblast_5fstep(s, v52, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::Pow, &[v49, v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_core(EvalOp::Eq, &[v47, v69]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_24_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v42 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24bv_5fbitwidth(s, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_core(EvalOp::IsNeg, &[v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match if_23_eo__24bv_5fmk_5fbitblast_5fstep(s, v44, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v71)
}
Some(false) => {
let v72 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24bv_5fbitwidth(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v72, v74) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v75)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_25_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v83 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(v83)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v84)
}
Some(false) => {
let v85 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(v85)) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match eo__24bv_5fbitwidth(s, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_core(EvalOp::Log, &[v86, v88]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v89)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_26_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v80 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match eo__24bv_5fbitwidth(s, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::IsNeg, &[v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match if_25_eo__24bv_5fmk_5fbitblast_5fstep(s, v82, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v90)
}
Some(false) => {
let v91 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24bv_5fbitwidth(s, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v91, v93) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v94)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_27_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v103)
}
Some(false) => {
let v104 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.literal(Lit::Numeral(v104)) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24bv_5fbitwidth(s, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_core(EvalOp::Log, &[v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v108)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_28_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v99 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match eo__24bv_5fbitwidth(s, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.builtin_core(EvalOp::IsNeg, &[v100]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match if_27_eo__24bv_5fmk_5fbitblast_5fstep(s, v101, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v109)
}
Some(false) => {
let v110 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24bv_5fbitwidth(s, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v110, v112) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v113)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_29_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v77 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match eo__24bv_5fbitwidth(s, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_core(EvalOp::IsZ, &[v78]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match if_26_eo__24bv_5fmk_5fbitblast_5fstep(s, v79, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v95)
}
Some(false) => {
let v96 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match eo__24bv_5fbitwidth(s, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.builtin_core(EvalOp::IsZ, &[v97]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match if_28_eo__24bv_5fmk_5fbitblast_5fstep(s, v98, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(v115)) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.builtin_core(EvalOp::Add, &[v114, v116]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v117)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_31_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v40: Term, v5: Term, v2: Term, v38: Term, v36: Term) -> CheckResult<Option<Term>> {
let v41 = match s.builtin_core(EvalOp::IsZ, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match if_24_eo__24bv_5fmk_5fbitblast_5fstep(s, v41, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match if_29_eo__24bv_5fmk_5fbitblast_5fstep(s, v76, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec(s, v5, v2, v38, v118, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match eo__24bv_5fbitwidth(s, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.builtin_list(EvalOp::ListRepeat, &[v121, v122, v124]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24bv_5fbitblast_5fapply_5fite(s, v36, v120, v125) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v126))
}
pub(super) fn more_30_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v14: Term, v13: Term, v5: Term, v11: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::ToBin, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Length, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_20_eo__24bv_5fmk_5fbitblast_5fstep(s, v18, v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24bv_5fconst_5fto_5fbitlist_5frec(s, v11, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24bv_5fbitblast_5fult(s, v2, v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24bv_5fbitwidth(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24bv_5fmk_5fbitblast_5fstep(s, v40, v5, v2, v38, v36)
}
pub(super) fn case_20_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitwidth(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::ToBin, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24bv_5fmk_5fbitblast_5fstep(s, v14, v13, v5, v11, v2)
}
pub(super) fn requires_32_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v18: Term, v19: Term, v5: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24bv_5fbitwidth(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24bv_5fbitwidth(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::ToBin, &[v24, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Length, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListRepeat, &[v20, v22, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24iota_5frec(s, v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn if_33_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v56 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Numeral(v56)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
Some(false) => {
let v58 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(v58)) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24bv_5fbitwidth(s, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.builtin_core(EvalOp::Log, &[v59, v61]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_34_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v53 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24bv_5fbitwidth(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_core(EvalOp::IsNeg, &[v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match if_33_eo__24bv_5fmk_5fbitblast_5fstep(s, v55, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v63)
}
Some(false) => {
let v64 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24bv_5fbitwidth(s, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v67)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_35_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v45 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
Some(false) => {
let v46 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24bv_5fbitwidth(s, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(v48)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24bv_5fbitwidth(s, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_core(EvalOp::IsZ, &[v51]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match if_34_eo__24bv_5fmk_5fbitblast_5fstep(s, v52, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_core(EvalOp::Pow, &[v49, v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_core(EvalOp::Eq, &[v47, v69]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_36_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v42 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24bv_5fbitwidth(s, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_core(EvalOp::IsNeg, &[v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match if_35_eo__24bv_5fmk_5fbitblast_5fstep(s, v44, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v71)
}
Some(false) => {
let v72 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24bv_5fbitwidth(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v72, v74) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v75)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_37_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v83 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(v83)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v84)
}
Some(false) => {
let v85 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(v85)) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match eo__24bv_5fbitwidth(s, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_core(EvalOp::Log, &[v86, v88]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v89)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_38_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v80 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match eo__24bv_5fbitwidth(s, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_core(EvalOp::IsNeg, &[v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match if_37_eo__24bv_5fmk_5fbitblast_5fstep(s, v82, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v90)
}
Some(false) => {
let v91 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24bv_5fbitwidth(s, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v91, v93) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v94)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_39_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v103)
}
Some(false) => {
let v104 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.literal(Lit::Numeral(v104)) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24bv_5fbitwidth(s, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_core(EvalOp::Log, &[v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v108)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_40_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v99 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match eo__24bv_5fbitwidth(s, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.builtin_core(EvalOp::IsNeg, &[v100]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match if_39_eo__24bv_5fmk_5fbitblast_5fstep(s, v101, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v109)
}
Some(false) => {
let v110 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24bv_5fbitwidth(s, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v110, v112) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v113)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_41_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v77 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match eo__24bv_5fbitwidth(s, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_core(EvalOp::IsZ, &[v78]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match if_38_eo__24bv_5fmk_5fbitblast_5fstep(s, v79, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v95)
}
Some(false) => {
let v96 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match eo__24bv_5fbitwidth(s, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.builtin_core(EvalOp::IsZ, &[v97]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match if_40_eo__24bv_5fmk_5fbitblast_5fstep(s, v98, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(v115)) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.builtin_core(EvalOp::Add, &[v114, v116]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v117)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
if a3 != a2 { return Ok(None); }
Ok(Some(Next::Done(a0)))
}
pub(super) fn if_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(v9)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Pow, &[v12, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.builtin_core(EvalOp::IsNeg, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s, v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v1 { return Ok(None); }
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Binary(BitVec::new(0, &v2))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$bv_mk_bitblast_step_shl_rec_step"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(41), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(41), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v15 { return Ok(None); }
let v16 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, v17, a3, v12, v5, v16, v2, v9)
}
pub(super) fn case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, a2, v15, v2, a1, a3, v13)
}
pub(super) fn more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s: &mut Store, v17: Term, a3: Term, v12: Term, v5: Term, v16: Term, v2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v17, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v16, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, v2, v9, v23, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s: &mut Store, a2: Term, v15: Term, v2: Term, a1: Term, a3: Term, v13: Term) -> CheckResult<Option<Term>> {
let v16 = match s.builtin_core(EvalOp::Add, &[a2, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, v2, a1, v16, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsZ, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s, v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec_5fstep(s, a0, a0, v17, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Add, &[a2, v20]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v18, v2, v21, a3])))
}
pub(super) fn step_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Next<[Term; 4]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s, a0, a1, a2, a3) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
a3 = next[3];
}
Err(e) => return Err(e),
}
}
}
// EO program "$bv_mk_bitblast_step_shl_rec"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(40), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(40), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn more_43_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v40: Term, v5: Term, v2: Term, v38: Term, v36: Term) -> CheckResult<Option<Term>> {
let v41 = match s.builtin_core(EvalOp::IsZ, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match if_36_eo__24bv_5fmk_5fbitblast_5fstep(s, v41, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match if_41_eo__24bv_5fmk_5fbitblast_5fstep(s, v76, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match eo__24bv_5fmk_5fbitblast_5fstep_5fshl_5frec(s, v5, v2, v38, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match eo__24bv_5fbitwidth(s, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_list(EvalOp::ListRepeat, &[v120, v121, v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match eo__24bv_5fbitblast_5fapply_5fite(s, v36, v119, v124) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v125))
}
pub(super) fn more_42_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v14: Term, v13: Term, v5: Term, v11: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::ToBin, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Length, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_32_eo__24bv_5fmk_5fbitblast_5fstep(s, v18, v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24bv_5fconst_5fto_5fbitlist_5frec(s, v11, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24bv_5fbitblast_5fult(s, v2, v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24bv_5fbitwidth(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_43_eo__24bv_5fmk_5fbitblast_5fstep(s, v40, v5, v2, v38, v36)
}
pub(super) fn case_21_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitwidth(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitwidth(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::ToBin, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_42_eo__24bv_5fmk_5fbitblast_5fstep(s, v14, v13, v5, v11, v2)
}
pub(super) fn case_22_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListSingletonElim, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Binary(BitVec::new(0, &v12))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_23_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvultbv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fbitblast_5fult(s, v5, v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Binary(BitVec::new(0, &v11))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn cases_0_5_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_20_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_21_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_22_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_23_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_44_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Binary(BitVec::new(0, &v15))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_24_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsltbv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListRev, &[v8, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_list(EvalOp::ListRev, &[v10, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitblast_5fslt_5fimpl(s, v9, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v7, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_44_eo__24bv_5fmk_5fbitblast_5fstep(s, v14)
}
pub(super) fn case_25_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_sign_5fextend, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListRev, &[v6, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24bv_5fbitblast_5fhead(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListRepeat, &[v5, v8, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24bv_5fbitblast_5fconcat(s, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn requires_45_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v2: Term, v3: Term, a0: Term) -> CheckResult<Term> {
if v2 != v3 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v4 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(v5)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Length, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListRepeat, &[v4, v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(v9)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24iota_5frec(s, v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
pub(super) fn requires_46_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, v16: Term, v17: Term, a0: Term) -> CheckResult<Term> {
if v16 != v17 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v16) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v18 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24bv_5fbitwidth(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListRepeat, &[v18, v20, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(v24)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24iota_5frec(s, v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Binary(BitVec::new(0, &v5))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
// EO program "$bv_mk_bitblast_step_var_rec"
pub fn eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(44), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(44), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40bit, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn if_47_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.builtin_core(EvalOp::Length, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::IsNeg, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match requires_45_eo__24bv_5fmk_5fbitblast_5fstep(s, v2, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fconst_5fto_5fbitlist_5frec(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::IsNeg, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_46_eo__24bv_5fmk_5fbitblast_5fstep(s, v16, v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_26_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::IsBin, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match if_47_eo__24bv_5fmk_5fbitblast_5fstep(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn cases_0_6_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_24_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_25_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_26_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_6_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_1_0_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_1_1_eo__24bv_5fmk_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_mk_bitblast_step"
pub fn eo__24bv_5fmk_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fmk_5fbitblast_5fstep(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, v34: Term, v35: Term, v4: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v34 != v35 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v34) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v36 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_core(EvalOp::Length, &[v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListRepeat, &[v36, v38, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(v44)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match eo__24iota_5frec(s, v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v46)
}
pub(super) fn more_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s: &mut Store, a5: Term, v14: Term, a1: Term, a0: Term, v12: Term, v7: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_extract, &[a5, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5fnil(s, a0, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v7, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v2, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Binary(BitVec::new(0, &v22))) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Binary(BitVec::new(0, &v0))) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_extract, &[a5, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_extract, &[a5, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(a0, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, a5, v14, a1, a0, v12, v7, v2)
}
// EO program "$bv_mk_bitwise_slicing_rec"
pub fn eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4, a5, a6];
match s.cached_program(ProgramId(46), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(46), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
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
let stuck5 = match s.is_stuck(a5) { Ok(v) => v, Err(e) => return Err(e) };
if stuck5 { return Ok(s.stuck()); }
let stuck6 = match s.is_stuck(a6) { Ok(v) => v, Err(e) => return Err(e) };
if stuck6 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::Eq, &[v5, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match if_2_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, v7, a6, a0, a1, a2, v2, v5, a5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v40))
}
pub(super) fn more_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s: &mut Store, a6: Term, v26: Term, a5: Term, a1: Term, a0: Term, v24: Term, v18: Term, v12: Term, a2: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let v27 = match s.builtin_core(EvalOp::Add, &[a6, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_extract, &[a5, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5ftypeof(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fnil(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v24, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v18, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v12, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(v35)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::Add, &[a6, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, a0, a1, a2, v2, v5, a6, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v34, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v39)
}
pub(super) fn if_2_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s: &mut Store, condition: Term, a6: Term, a0: Term, a1: Term, a2: Term, v2: Term, v5: Term, a5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[a6, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, a0, a1, a2, v2, v5, a5, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Add, &[a6, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_extract, &[a5, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(a0, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Add, &[a6, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_extract, &[a5, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(a0, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, a6, v26, a5, a1, a0, v24, v18, v12, a2, v2, v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_4_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, v78: Term, v2: Term, v4: Term, v18: Term, v25: Term, v49: Term, v70: Term, v77: Term) -> CheckResult<Term> {
let v79 = match s.apply(v78, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_core(EvalOp::Length, &[v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Numeral(v82)) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_core(EvalOp::Add, &[v81, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match eo__24bv_5fmk_5fbitwise_5fslicing_5frec(s, v4, v18, v25, v49, v70, v77, v84) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v85)
}
pub(super) fn more_3_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, v63: Term, v52: Term, v59: Term, v4: Term, v5: Term, v2: Term, v18: Term, v25: Term, v49: Term) -> CheckResult<Term> {
let v64 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(v64)) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_core(EvalOp::Add, &[v63, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_core(EvalOp::Extract, &[v52, v59, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Binary(BitVec::new(1, &v68))) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_core(EvalOp::Eq, &[v67, v69]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_core(EvalOp::Length, &[v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::Numeral(v75)) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.builtin_core(EvalOp::Add, &[v74, v76]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24bv_5fmk_5fbitwise_5fslicing(s, v78, v2, v4, v18, v25, v49, v70, v77)
}
pub(super) fn more_2_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, v50: Term, v2: Term, v4: Term, v5: Term, v18: Term, v25: Term, v49: Term) -> CheckResult<Term> {
let v51 = match s.apply(v50, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.builtin_core(EvalOp::Length, &[v55]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_core(EvalOp::Add, &[v56, v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.builtin_core(EvalOp::Length, &[v62]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24bv_5fmk_5fbitwise_5fslicing(s, v63, v52, v59, v4, v5, v2, v18, v25, v49)
}
pub(super) fn more_1_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, v27: Term, v2: Term, v4: Term, v5: Term, v26: Term, v18: Term, v25: Term) -> CheckResult<Term> {
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::Length, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::IsNeg, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match requires_0_eo__24bv_5fmk_5fbitwise_5fslicing(s, v34, v35, v4, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match eo__24bv_5fconst_5fto_5fbitlist_5frec(s, v29, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_list(EvalOp::ListRev, &[v26, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fmk_5fbitwise_5fslicing(s, v50, v2, v4, v5, v18, v25, v49)
}
pub(super) fn requires_5_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, v14: Term, v15: Term, v4: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24bv_5fget_5ffirst_5fconst_5fchild(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListErase, &[v4, v20, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListSingletonElim, &[v4, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__40from_5fbools, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fmk_5fbitwise_5fslicing(s, v27, v2, v4, v5, v26, v18, v25)
}
pub(super) fn more_6_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, v14: Term, v15: Term, v4: Term, v5: Term, v2: Term, v6: Term) -> CheckResult<Option<Term>> {
let v86 = match requires_5_eo__24bv_5fmk_5fbitwise_5fslicing(s, v14, v15, v4, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.builtin_list(EvalOp::ListSingletonElim, &[v6, v86]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v87))
}
pub(super) fn case_0_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v4, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Eq, &[v4, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Or, &[v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Eq, &[v4, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Or, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24bv_5fmk_5fbitwise_5fslicing(s, v14, v15, v4, v5, v2, v6)
}
pub(super) fn body_eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fmk_5fbitwise_5fslicing(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$bv_mk_bitwise_slicing"
pub fn eo__24bv_5fmk_5fbitwise_5fslicing(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24bv_5fmk_5fbitwise_5fslicing(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
Ok(Some(Next::Done(a3)))
}
pub(super) fn more_3_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, v53: Term, v56: Term, a1: Term, v50: Term, v49: Term, v33: Term, v23: Term, v22: Term, a0: Term, v20: Term, v2: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v57 = match s.construct(Constructor::eo_extract, &[v53, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24eo_5ftypeof(s, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24eo_5fnil(s, v50, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v49, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v33, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v23, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Binary(BitVec::new(1, &v64))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v63, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v22, v66) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, a1, v20, v67, v2, a5])))
}
pub(super) fn more_2_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, v39: Term, v41: Term, a0: Term, v37: Term, v36: Term, v34: Term, v5: Term, a1: Term, v33: Term, v23: Term, v22: Term, v20: Term, v2: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v42 = match s.construct(Constructor::eo_extract, &[v39, v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v37, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Binary(BitVec::new(1, &v45))) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v36, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v34, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(v51)) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_core(EvalOp::Add, &[v5, v52]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(v54)) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.builtin_core(EvalOp::Add, &[v5, v55]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24bv_5fsmulo_5felim_5frec(s, v53, v56, a1, v50, v49, v33, v23, v22, a0, v20, v2, a5)
}
pub(super) fn more_1_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, v5: Term, v29: Term, v27: Term, a1: Term, v24: Term, a2: Term, a5: Term, a0: Term, v23: Term, v22: Term, v20: Term, v2: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v30 = match s.builtin_core(EvalOp::Add, &[v5, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_extract, &[v27, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v24, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Add, &[a5, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_core(EvalOp::Add, &[a5, v40]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fsmulo_5felim_5frec(s, v39, v41, a0, v37, v36, v34, v5, a1, v33, v23, v22, v20, v2, a5)
}
pub(super) fn more_0_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, v14: Term, a0: Term, v9: Term, v8: Term, a3: Term, v5: Term, a1: Term, a2: Term, a5: Term, v2: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Binary(BitVec::new(1, &v17))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v8, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Add, &[v5, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(v28)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fsmulo_5felim_5frec(s, v5, v29, v27, a1, v24, a2, a5, a0, v23, v22, v20, v2)
}
pub(super) fn case_1_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Add, &[a5, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[a5, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_extract, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fsmulo_5felim_5frec(s, v14, a0, v9, v8, a3, v5, a1, a2, a5, v2)
}
pub(super) fn step_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Next<[Term; 6]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
let stuck4 = match s.is_stuck(a4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck4 { return Ok(Next::Done(s.stuck())); }
let stuck5 = match s.is_stuck(a5) { Ok(v) => v, Err(e) => return Err(e) };
if stuck5 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24bv_5fsmulo_5felim_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fsmulo_5felim_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term, mut a5: Term) -> CheckResult<Term> {
loop {
match step_eo__24bv_5fsmulo_5felim_5frec(s, a0, a1, a2, a3, a4, a5) {
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
// EO program "$bv_smulo_elim_rec"
pub fn eo__24bv_5fsmulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4, a5];
match s.cached_program(ProgramId(51), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fsmulo_5felim_5frec(s, a0, a1, a2, a3, a4, a5);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(51), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24bv_5fumulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
Ok(Some(a3))
}
// EO program "$bv_umulo_elim_rec"
pub fn eo__24bv_5fumulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4, a5];
match s.cached_program(ProgramId(52), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24bv_5fumulo_5felim_5frec(s, a0, a1, a2, a3, a4, a5);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(52), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24bv_5fumulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
let stuck5 = match s.is_stuck(a5) { Ok(v) => v, Err(e) => return Err(e) };
if stuck5 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24bv_5fumulo_5felim_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24bv_5fumulo_5felim_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24bv_5fumulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_extract, &[v5, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24bv_5fumulo_5felim_5frec(s, v5, a1, v14, v13, v11, v7, a5, a0, a2, a3, v2)
}
pub(super) fn more_3_eo__24bv_5fumulo_5felim_5frec(s: &mut Store, a0: Term, a1: Term, v54: Term, a3: Term, v2: Term, a5: Term, v21: Term) -> CheckResult<Option<Term>> {
let v55 = match eo__24bv_5fumulo_5felim_5frec(s, a0, a1, v54, a3, v2, a5) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v21, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v56))
}
pub(super) fn more_2_eo__24bv_5fumulo_5felim_5frec(s: &mut Store, v5: Term, v41: Term, a5: Term, a0: Term, v38: Term, v37: Term, v35: Term, a1: Term, a3: Term, v2: Term, v21: Term) -> CheckResult<Option<Term>> {
let v42 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_core(EvalOp::Add, &[v41, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(v44)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_core(EvalOp::Add, &[a5, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.builtin_core(EvalOp::Add, &[v46, v47]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_extract, &[v43, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24eo_5ftypeof(s, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24eo_5fnil(s, v38, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v37, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v35, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24bv_5fumulo_5felim_5frec(s, a0, a1, v54, a3, v2, a5, v21)
}
pub(super) fn more_1_eo__24bv_5fumulo_5felim_5frec(s: &mut Store, a5: Term, v5: Term, v27: Term, a0: Term, v22: Term, a2: Term, a1: Term, a3: Term, v2: Term, v21: Term) -> CheckResult<Option<Term>> {
let v28 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(v28)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Add, &[a5, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::Add, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_extract, &[v27, v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v22, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Numeral(v39)) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_core(EvalOp::Add, &[a5, v40]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24bv_5fumulo_5felim_5frec(s, v5, v41, a5, a0, v38, v37, v35, a1, a3, v2, v21)
}
pub(super) fn more_0_eo__24bv_5fumulo_5felim_5frec(s: &mut Store, v5: Term, a1: Term, v14: Term, v13: Term, v11: Term, v7: Term, a5: Term, a0: Term, a2: Term, a3: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_extract, &[v5, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5fnil(s, v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v13, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v7, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Add, &[a5, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Add, &[v25, v26]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24bv_5fumulo_5felim_5frec(s, a5, v5, v27, a0, v22, a2, a1, a3, v2, v21)
}
pub(super) fn if_0_eo__24chain_5fm_5fresolve_5ffinal(s: &mut Store, condition: Term, v5: Term, v12: Term, v9: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v5)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListDiff, &[v16, a0, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListConcat, &[v15, v20, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24chain_5fm_5fresolve_5ffinal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.builtin_core(EvalOp::Eq, &[a0, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_0_eo__24chain_5fm_5fresolve_5ffinal(s, v14, v5, v12, v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn body_eo__24chain_5fm_5fresolve_5ffinal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24chain_5fm_5fresolve_5ffinal(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$chain_m_resolve_final"
pub fn eo__24chain_5fm_5fresolve_5ffinal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24chain_5fm_5fresolve_5ffinal(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24chain_5fm_5fresolve_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v2 { return Ok(None); }
let v3 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn if_0_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, condition: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
Ok(a3)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, condition: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a3)
}
Some(false) => {
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, condition: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
Some(false) => {
Ok(a3)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, condition: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a3)
}
Some(false) => {
let v33 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v34)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_4_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, v32: Term, v35: Term, v2: Term, v31: Term) -> CheckResult<Term> {
let v36 = match s.apply(v32, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v31, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
pub(super) fn if_5_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, condition: Term, v5: Term, a2: Term, a3: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_1_eo__24chain_5fm_5fresolve_5frec_5fstep(s, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_2_eo__24chain_5fm_5fresolve_5frec_5fstep(s, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListDiff, &[v22, a1, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_list(EvalOp::ListConcat, &[v21, v29, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v20, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match if_3_eo__24chain_5fm_5fresolve_5frec_5fstep(s, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24chain_5fm_5fresolve_5frec_5fstep(s, v32, v35, v2, v31)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v9 = match if_0_eo__24chain_5fm_5fresolve_5frec_5fstep(s, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Eq, &[v9, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match if_5_eo__24chain_5fm_5fresolve_5frec_5fstep(s, v10, v5, a2, a3, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn body_eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24chain_5fm_5fresolve_5frec_5fstep(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$chain_m_resolve_rec_step"
pub fn eo__24chain_5fm_5fresolve_5frec_5fstep(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24chain_5fm_5fresolve_5frec_5fstep(s, a0, a1, a2, a3);
s.leave();
result
}
// EO program "$chain_m_resolve_rec"
pub fn eo__24chain_5fm_5fresolve_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(55), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24chain_5fm_5fresolve_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(55), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24chain_5fm_5fresolve_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24chain_5fm_5fresolve_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24chain_5fm_5fresolve_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24chain_5fm_5fresolve_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_0_eo__24chain_5fm_5fresolve_5frec(s, v2, v9, v16, v5, v12, v19)
}
pub(super) fn more_0_eo__24chain_5fm_5fresolve_5frec(s: &mut Store, v2: Term, v9: Term, v16: Term, v5: Term, v12: Term, v19: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24chain_5fm_5fresolve_5frec(s, v2, v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24chain_5fm_5fresolve_5frec_5fstep(s, v21, v5, v12, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24chain_5fm_5fresolve(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24chain_5fm_5fresolve_5frec(s, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24chain_5fm_5fresolve_5ffinal(s, v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24chain_5fm_5fresolve(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24chain_5fm_5fresolve(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$chain_m_resolve"
pub fn eo__24chain_5fm_5fresolve(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24chain_5fm_5fresolve(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24compute_5fcard(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(v1)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn if_0_eo__24compute_5fcard(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Pow, &[v9, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24compute_5fcard(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_0_eo__24compute_5fcard(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24compute_5fcard(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.builtin_core(EvalOp::IsZ, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_1_eo__24compute_5fcard(s, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn body_eo__24compute_5fcard(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24compute_5fcard(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24compute_5fcard(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$compute_card"
pub fn eo__24compute_5fcard(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24compute_5fcard(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListConcat, &[v13, v16, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, a1, v17])))
}
pub(super) fn if_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, condition: Term, v1: Term, v2: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fVar, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListFind, &[v8, a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fVar, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListFind, &[v3, a1, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::IsNeg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v6, v1, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v12)))
}
pub(super) fn requires_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, v1: Term, v2: Term) -> CheckResult<Term> {
if v1 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
pub(super) fn case_2_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fVar, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListFind, &[v3, a1, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::IsNeg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Not, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v7)))
}
pub(super) fn case_3_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__40quantifiers_5fskolemize, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([v1, a1])))
}
pub(super) fn case_5_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
// EO program "$is_closed_rec"
pub fn eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(891), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fclosed_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(891), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24is_5fclosed_5frec(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24is_5fclosed_5frec(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match cases_0_0_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_0_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match eo__24is_5fclosed_5frec(s, v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListConcat, &[v14, v17, a1]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24is_5fclosed_5frec(s, v2, v18, v13)
}
pub(super) fn case_1_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24is_5fclosed_5frec(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24is_5fclosed_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_4_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__40re_5funfold_5fpos_5fcomponent, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24is_5fclosed_5frec(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24is_5fclosed_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::And, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn cases_0_0_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if let Some(found) = match case_0_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24is_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if let Some(found) = match case_4_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24is_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24is_5fclosed_5frec(s: &mut Store, v2: Term, v18: Term, v13: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v19 = match eo__24is_5fclosed_5frec(s, v2, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::And, &[v13, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v20)))
}
pub(super) fn case_3_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24is_5fclosed_5frec(s, a0, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match requires_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
// EO program "$contains_atomic_term_list_free_rec"
pub fn eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(58), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(58), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a1, a2) {
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
pub(super) fn step_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v1, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v3, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn if_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s: &mut Store, condition: Term, v2: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
Some(false) => {
let v5 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
Ok(Some(a2))
}
pub(super) fn case_1_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if a2 != a1 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn more_0_eo__24re_5fac_5fmerge(s: &mut Store, v17: Term, v8: Term, a0: Term, v16: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v17, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListConcat, &[a0, v16, v18]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_3_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
if v10 != a0 { return Ok(None); }
let v12 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(a0, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListDiff, &[a0, v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(a0, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24re_5fac_5fmerge(s, v17, v8, a0, v16)
}
pub(super) fn cases_0_0_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_1_eo__24re_5fac_5fmerge(s: &mut Store, condition: Term, a0: Term, a2: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.apply(a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_4_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListFind, &[a0, v7, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsNeg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_1_eo__24re_5fac_5fmerge(s, v9, a0, a2, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn if_2_eo__24re_5fac_5fmerge(s: &mut Store, condition: Term, a0: Term, a1: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.apply(a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_5_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match s.apply(a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListFind, &[a0, v7, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsNeg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_2_eo__24re_5fac_5fmerge(s, v9, a0, a1, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_6_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.apply(a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_RegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fnil(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_1_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24re_5fac_5fmerge(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$re_ac_merge"
pub fn eo__24re_5fac_5fmerge(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24re_5fac_5fmerge(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn more_0_eo__24re_5fconcat_5fmerge(s: &mut Store, v12: Term, v9: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
let v18 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListConcat, &[v14, v17, v20]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24re_5fconcat_5fmerge(s, v12, v9, v14, v17)
}
pub(super) fn case_1_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_3_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn cases_0_0_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
Ok(Some(a0))
}
pub(super) fn case_5_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_1_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24re_5fconcat_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$re_concat_merge"
pub fn eo__24re_5fconcat_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24re_5fconcat_5fmerge(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn requires_0_eo__24re_5fnullable(s: &mut Store, v4: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v4 != v5 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v6 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Eq, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
pub(super) fn case_3_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.builtin_core(EvalOp::IsStr, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match requires_0_eo__24re_5fnullable(s, v4, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_0_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_5_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
// EO program "$re_nullable"
pub fn eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(951), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5fnullable(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(951), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_6_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24re_5fnullable(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24re_5fnullable(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Or, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_7_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24re_5fnullable(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24re_5fnullable(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::And, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_8_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24re_5fnullable(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24re_5fnullable(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::And, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_9_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24re_5fnullable(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Not, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_1_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24re_5fnullable(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24re_5fnullable(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_5_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn if_1_eo__24derivative(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Length, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Add, &[v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Extract, &[v2, v12, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v10, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_6_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Extract, &[v2, v5, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v8, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_1_eo__24derivative(s, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn if_2_eo__24derivative(s: &mut Store, condition: Term, a0: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Gt, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24derivative(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.builtin_core(EvalOp::ToInt, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Gt, &[v19, v20]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24derivative(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
Some(false) => {
let v27 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24derivative(s: &mut Store, v14: Term, v22: Term) -> CheckResult<Option<Term>> {
let v23 = match s.builtin_core(EvalOp::And, &[v14, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_4_eo__24derivative(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_7_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_2_eo__24derivative(s, v9, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::ToInt, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Eq, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_3_eo__24derivative(s, v17, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24derivative(s, v14, v22)
}
pub(super) fn case_8_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_9_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_10_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn cases_0_2_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$derivative"
pub fn eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(59), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24derivative(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(59), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24derivative(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24derivative(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5fac_5fmerge(s, v7, v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_1_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24re_5fnullable(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24derivative(s, v7, a0, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_2_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24derivative(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24derivative(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5fac_5fmerge(s, v7, v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_3_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24derivative(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_4_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24derivative(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24re_5fconcat_5fmerge(s, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn cases_0_0_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24derivative(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24derivative(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24derivative(s: &mut Store, condition: Term, a0: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24derivative(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24derivative(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24re_5fconcat_5fmerge(s, v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24re_5fac_5fmerge(s, v8, v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match eo__24derivative(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24re_5fconcat_5fmerge(s, v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24tuple_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$tuple_arg_list"
pub fn eo__24tuple_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1081), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24tuple_5farg_5flist(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1081), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24tuple_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24tuple_5farg_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24tuple_5farg_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24tuple_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24tuple_5farg_5flist(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_0_eo__24dt_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24tuple_5farg_5flist(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_0_eo__24get_5farg_5flist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v1, v5])))
}
pub(super) fn case_1_eo__24get_5farg_5flist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
Ok(Some(Next::Done(a1)))
}
pub(super) fn step_eo__24get_5farg_5flist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24get_5farg_5flist_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24get_5farg_5flist_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24get_5farg_5flist_5frec(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24get_5farg_5flist_5frec(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$get_arg_list_rec"
pub fn eo__24get_5farg_5flist_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(879), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5farg_5flist_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(879), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24dt_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24get_5farg_5flist_5frec(s, a0, v0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24dt_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24dt_5farg_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5farg_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$dt_arg_list"
pub fn eo__24dt_5farg_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24dt_5farg_5flist(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24dt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v4 { return Ok(None); }
let v5 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$dt_collapse_updater_rhs"
pub fn eo__24dt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(61), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24dt_5fcollapse_5fupdater_5frhs(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(61), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24dt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24dt_5fcollapse_5fupdater_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5fcollapse_5fupdater_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24dt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Add, &[a2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24dt_5fcollapse_5fupdater_5frhs(s, v1, a1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_0_eo__24dt_5feq_5fcons(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
Ok(Some(Next::Again([v1, a1])))
}
pub(super) fn case_1_eo__24dt_5feq_5fcons(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
Ok(Some(Next::Again([a0, v1])))
}
pub(super) fn if_0_eo__24dt_5feq_5fcons(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
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
pub(super) fn if_1_eo__24dt_5feq_5fcons(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
Some(false) => {
let v3 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::IsEq, &[a0, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24dt_5feq_5fcons(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24dt_5feq_5fcons(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match eo__24eo_5fdt_5fselectors(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::IsOk, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24dt_5feq_5fcons(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::IsEq, &[a1, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_2_eo__24dt_5feq_5fcons(s, v17, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_4_eo__24dt_5feq_5fcons(s: &mut Store, v22: Term, v23: Term) -> CheckResult<Term> {
if v22 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
pub(super) fn if_5_eo__24dt_5feq_5fcons(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IsEq, &[a1, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_3_eo__24dt_5feq_5fcons(s, v14, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match requires_4_eo__24dt_5feq_5fcons(s, v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_6_eo__24dt_5feq_5fcons(s: &mut Store, v9: Term, v10: Term, a0: Term, a1: Term) -> CheckResult<Term> {
if v9 != v10 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v11 = match s.builtin_core(EvalOp::Eq, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_5_eo__24dt_5feq_5fcons(s, v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn case_2_eo__24dt_5feq_5fcons(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::IsEq, &[a0, v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_1_eo__24dt_5feq_5fcons(s, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_6_eo__24dt_5feq_5fcons(s, v9, v10, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v27)))
}
pub(super) fn step_eo__24dt_5feq_5fcons(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24dt_5feq_5fcons(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5feq_5fcons(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24dt_5feq_5fcons(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24dt_5feq_5fcons(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24dt_5feq_5fcons(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$dt_eq_cons"
pub fn eo__24dt_5feq_5fcons(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(63), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24dt_5feq_5fcons(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(63), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24dt_5ffind_5fcycle(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
Ok(Some(a3))
}
pub(super) fn case_0_eo__24is_5fcons_5fapp(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
Ok(Some(Next::Again([v1])))
}
pub(super) fn if_0_eo__24is_5fcons_5fapp(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
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
pub(super) fn if_1_eo__24is_5fcons_5fapp(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
Some(false) => {
let v3 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::IsEq, &[a0, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24is_5fcons_5fapp(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24is_5fcons_5fapp(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::IsEq, &[a0, v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_1_eo__24is_5fcons_5fapp(s, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn step_eo__24is_5fcons_5fapp(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24is_5fcons_5fapp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fcons_5fapp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24is_5fcons_5fapp(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24is_5fcons_5fapp(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
// EO program "$is_cons_app"
pub fn eo__24is_5fcons_5fapp(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(892), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fcons_5fapp(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(892), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_2_eo__24dt_5ffind_5fcycle(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$dt_find_cycle"
pub fn eo__24dt_5ffind_5fcycle(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(64), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24dt_5ffind_5fcycle(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(64), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24dt_5ffind_5fcycle(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24dt_5ffind_5fcycle(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5ffind_5fcycle(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24dt_5ffind_5fcycle(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24dt_5ffind_5fcycle(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v3 { return Ok(None); }
let v4 = match eo__24is_5fcons_5fapp(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24dt_5ffind_5fcycle(s, v2, a1, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24dt_5ffind_5fcycle(s, v6, v1, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn if_0_eo__24dt_5ffind_5fcycle(s: &mut Store, condition: Term, v1: Term, a1: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24dt_5ffind_5fcycle(s, v1, a1, v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24dt_5fget_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v11)))
}
pub(super) fn case_1_eo__24dt_5fget_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_2_eo__24dt_5fget_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
Ok(Some(Next::Again([v1])))
}
pub(super) fn case_1_eo__24eo_5fdatatype_5fconstructors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_datatype_constructors_rec"
pub fn eo__24eo_5fdatatype_5fconstructors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(74), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdatatype_5fconstructors_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(74), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdatatype_5fconstructors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdatatype_5fconstructors_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdatatype_5fconstructors_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fdatatype_5fconstructors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fDtCons, &[a0, a1, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::NatSucc, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fdatatype_5fconstructors_5frec(s, a0, a1, v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fdt_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDatatypeType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fdd_5flookup(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fdatatype_5fconstructors_5frec(s, v1, v2, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fdt_5fconstructors_5fmain(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
Ok(s.stuck())
}
// EO program "$eo_dt_constructors_main"
pub fn eo__24eo_5fdt_5fconstructors_5fmain(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdt_5fconstructors_5fmain(s, a0);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5fdt_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fdt_5fconstructors_5fmain(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fdt_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fdt_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdt_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_dt_constructors"
pub fn eo__24eo_5fdt_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdt_5fconstructors(s, a0);
s.leave();
result
}
pub(super) fn case_3_eo__24dt_5fget_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match eo__24eo_5fdt_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24dt_5fget_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24dt_5fget_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5fget_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24dt_5fget_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24dt_5fget_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24dt_5fget_5fconstructors(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24dt_5fget_5fconstructors(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
// EO program "$dt_get_constructors"
pub fn eo__24dt_5fget_5fconstructors(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(65), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24dt_5fget_5fconstructors(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(65), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24tuple_5fget_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$tuple_get_selectors_rec"
pub fn eo__24tuple_5fget_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1083), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24tuple_5fget_5fselectors_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1083), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24tuple_5fget_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24tuple_5fget_5fselectors_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24tuple_5fget_5fselectors_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24tuple_5fget_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_tuple_2eselect, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[a1, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24tuple_5fget_5fselectors_5frec(s, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24dt_5fget_5fselectors(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24tuple_5fget_5fselectors_5frec(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_1_eo__24dt_5fget_5fselectors(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24dt_5fget_5fselectors(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fdt_5fselectors(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24dt_5fget_5fselectors(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24dt_5fget_5fselectors(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5fget_5fselectors(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24dt_5fget_5fselectors(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$dt_get_selectors"
pub fn eo__24dt_5fget_5fselectors(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24dt_5fget_5fselectors(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24dt_5fget_5fselectors_5fof_5fapp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
Ok(Some(Next::Again([a0, v1])))
}
pub(super) fn case_1_eo__24dt_5fget_5fselectors_5fof_5fapp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match eo__24dt_5fget_5fselectors(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24dt_5fget_5fselectors_5fof_5fapp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24dt_5fget_5fselectors_5fof_5fapp(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5fget_5fselectors_5fof_5fapp(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24dt_5fget_5fselectors_5fof_5fapp(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24dt_5fget_5fselectors_5fof_5fapp(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$dt_get_selectors_of_app"
pub fn eo__24dt_5fget_5fselectors_5fof_5fapp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(67), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24dt_5fget_5fselectors_5fof_5fapp(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(67), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24dt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v8 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
if v13 != v7 { return Ok(None); }
let v15 = match s.construct(Constructor::eo_update, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v17, v10, v18])))
}
pub(super) fn case_1_eo__24dt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v8 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.construct(Constructor::eo_update, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(a2, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v17, v10, v19])))
}
pub(super) fn case_2_eo__24dt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v8 { return Ok(None); }
Ok(Some(Next::Done(a2)))
}
pub(super) fn step_eo__24dt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24dt_5fupdater_5felim_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24dt_5fupdater_5felim_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24dt_5fupdater_5felim_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24dt_5fupdater_5felim_5frhs(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24dt_5fupdater_5felim_5frhs(s, a0, a1, a2) {
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
// EO program "$dt_updater_elim_rhs"
pub fn eo__24dt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(68), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24dt_5fupdater_5felim_5frhs(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(68), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24eo_5fStateObj_5fproven(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fso_2eassume, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fStateObj_5fproven(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fso_2eassume_5fpush, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(v1))
}
pub(super) fn case_2_eo__24eo_5fStateObj_5fproven(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fso_2eproven, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fStateObj_5fproven(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fStateObj_5fproven(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fStateObj_5fproven(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fStateObj_5fproven(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_StateObj_proven"
pub fn eo__24eo_5fStateObj_5fproven(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fStateObj_5fproven(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5finvoke_5fassume_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<FoldStep>> {
let v0 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(FoldStep::Done(a0)))
}
pub(super) fn case_0_eo__24eo_5fis_5fbool_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::Eq, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fis_5fbool_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5fbool_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_bool_type"
pub fn eo__24eo_5fis_5fbool_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5fbool_5ftype(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_2_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListConcat, &[v7, v5, a1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v8])))
}
pub(super) fn case_3_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListConcat, &[v7, v5, a1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v8])))
}
pub(super) fn case_5_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUOp1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([v2, a1])))
}
pub(super) fn case_8_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn cases_0_2_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if let Some(found) = match case_8_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$eo_is_closed_rec"
pub fn eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(92), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fis_5fclosed_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(92), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match cases_0_0_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo__24emb_5fVar, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Eq, &[v10, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24eo_5fis_5fclosed_5frec(s, v11, v1, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v15)))
}
pub(super) fn case_4_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24eo_5fis_5fclosed_5frec(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fis_5fclosed_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_6_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUOp2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fis_5fclosed_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fis_5fclosed_5frec(s, v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::And, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_7_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUOp3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match eo__24eo_5fis_5fclosed_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fis_5fclosed_5frec(s, v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fis_5fclosed_5frec(s, v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::And, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn cases_0_0_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if let Some(found) = match case_0_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if let Some(found) = match case_4_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, condition: Term, v1: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo__24emb_5fVar, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fis_5fclosed_5frec(s, v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5fis_5fclosed_5frec(s, a0, v0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_closed"
pub fn eo__24eo_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5fclosed(s, a0);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5finvoke_5fassume_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<FoldStep>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fis_5fbool_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fis_5fclosed(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(FoldStep::Push(v5, v1, v2)))
}
pub(super) fn step_eo__24eo_5finvoke_5fassume_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<FoldStep> {
if let Some(step) = match case_0_eo__24eo_5finvoke_5fassume_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(step); }
if let Some(step) = match case_1_eo__24eo_5finvoke_5fassume_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(step); }
Ok(FoldStep::Done(s.stuck()))
}
pub(super) fn scan_eo__24eo_5finvoke_5fassume_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<(Term, Vec<(Term, Term)>)> {
let mut pending = Vec::new();
let mut args = a1;
loop {
match step_eo__24eo_5finvoke_5fassume_5flist(s, a0, args) {
Ok(FoldStep::Done(state)) => return Ok((state, pending)),
Ok(FoldStep::Push(guard, term, tail)) => {
pending.push((guard, term));
args = tail;
}
Err(e) => return Err(e),
}
}
}
pub(super) fn case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fso_2eassume, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__24emb_5fs_2econs, &[v1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fpush_5finput_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_push_input_assume_check"
pub fn eo__24eo_5fpush_5finput_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fpush_5finput_5fassume_5fcheck(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn unwind_eo__24eo_5finvoke_5fassume_5flist(s: &mut Store, state: Term, pending: &[(Term, Term)]) -> CheckResult<Term> {
let mut state = state;
let mut i = pending.len();
while i > 0 {
i -= 1;
let (guard, term) = pending[i];
state = match eo__24eo_5fpush_5finput_5fassume_5fcheck(s, guard, term, state) { Ok(v) => v, Err(e) => return Err(e) };
}
Ok(state)
}
pub(super) fn body_eo__24eo_5finvoke_5fassume_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let scanned = match scan_eo__24eo_5finvoke_5fassume_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
unwind_eo__24eo_5finvoke_5fassume_5flist(s, scanned.0, &scanned.1)
}
// EO program "$eo_invoke_assume_list", compiled to an iterative guarded fold
pub fn eo__24eo_5finvoke_5fassume_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fassume_5flist(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fcmdl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(Next::Done(a0)))
}
pub(super) fn case_0_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fpush_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fso_2eassume_5fpush, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__24emb_5fs_2econs, &[v1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fpush_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fpush_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fpush_5fassume_5fcheck(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fpush_5fassume_5fcheck(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_push_assume_check"
pub fn eo__24eo_5fpush_5fassume_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fpush_5fassume_5fcheck(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmd_2eassume_5fpush, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5fis_5fbool_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fis_5fclosed(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::And, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fpush_5fassume_5fcheck(s, v4, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24eo_5fpush_5fproven_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fso_2eproven, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__24emb_5fs_2econs, &[v1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fpush_5fproven_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fpush_5fproven_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fpush_5fproven_5fcheck(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fpush_5fproven_5fcheck(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_push_proven_check"
pub fn eo__24eo_5fpush_5fproven_5fcheck(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fpush_5fproven_5fcheck(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fso_2eproven, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.builtin_core(EvalOp::Eq, &[v4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fpush_5fproven_5fcheck(s, v5, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_invoke_cmd_check_proven"
pub fn eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s, a0, a1);
s.leave();
result
}
pub(super) fn case_2_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmd_2echeck_5fproven, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24extract_5fantec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
if a1 != v2 { return Ok(None); }
Ok(Some(v5))
}
pub(super) fn case_0_eo__24extract_5fantec_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$extract_antec_rec"
pub fn eo__24extract_5fantec_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(872), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24extract_5fantec_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(872), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24extract_5fantec_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24extract_5fantec_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24extract_5fantec_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24extract_5fantec_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24extract_5fantec_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_1_eo__24extract_5fantec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24extract_5fantec_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24extract_5fantec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24extract_5fantec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24extract_5fantec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$extract_antec"
pub fn eo__24extract_5fantec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24extract_5fantec(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24run_5fprocess_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24extract_5fantec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24run_5fprocess_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24extract_5fantec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24run_5fprocess_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24run_5fprocess_5fscope(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24run_5fprocess_5fscope(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$run_process_scope"
pub fn eo__24run_5fprocess_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24run_5fprocess_5fscope(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fprocess_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24run_5fprocess_5fscope(s, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fprog_5fprocess_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fprocess_5fscope(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_process_scope"
pub fn eo__24eo_5fprog_5fprocess_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fprocess_5fscope(s, a0, a1);
s.leave();
result
}
// EO program "$eo_state_proven_nth", compiled to Store::state_nth
pub fn eo__24eo_5fstate_5fproven_5fnth(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = match s.state_nth(Constructor::eo__24emb_5fs_2econs, a0, a1) {
Ok(Some(element)) => eo__24eo_5fStateObj_5fproven(s, element),
Ok(None) => s.boolean(true),
Err(e) => Err(e),
};
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eprocess_5fscope, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fprog_5fprocess_5fscope(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_5feq(s: &mut Store, v12: Term, v16: Term, v5: Term, v11: Term, v8: Term, v2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v11, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v20, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_5feq(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_5feq(s, v12, v16, v5, v11, v8, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fite_5feq(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_5feq(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite_eq"
pub fn eo__24eo_5fprog_5fite_5feq(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_5feq(s, a0);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fite_5feq(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsplit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fsplit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsplit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_split"
pub fn eo__24eo_5fprog_5fsplit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsplit(s, a0);
s.leave();
result
}
pub(super) fn case_2_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esplit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fsplit(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fprog_5fresolution(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a1)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fresolution(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a1)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24to_5fclause(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_1_eo__24to_5fclause(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24to_5fclause(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24to_5fclause(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24to_5fclause(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24to_5fclause(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24to_5fclause(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$to_clause"
pub fn eo__24to_5fclause(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24to_5fclause(s, a0);
s.leave();
result
}
pub(super) fn if_2_eo__24eo_5fprog_5fresolution(s: &mut Store, condition: Term, v1: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24to_5fclause(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_1_eo__24eo_5fprog_5fresolution(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListErase, &[v11, v12, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fresolution(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
Ok(a1)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fresolution(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v26 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
Some(false) => {
Ok(a1)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24eo_5fprog_5fresolution(s: &mut Store, condition: Term, v3: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24to_5fclause(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_4_eo__24eo_5fprog_5fresolution(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListErase, &[v24, v25, v28]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24from_5fclause(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v5)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24from_5fclause(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_0_eo__24from_5fclause(s, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_1_eo__24from_5fclause(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
Ok(Some(a0))
}
pub(super) fn body_eo__24from_5fclause(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24from_5fclause(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24from_5fclause(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$from_clause"
pub fn eo__24from_5fclause(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24from_5fclause(s, a0);
s.leave();
result
}
pub(super) fn more_6_eo__24eo_5fprog_5fresolution(s: &mut Store, v31: Term) -> CheckResult<Option<Term>> {
let v32 = match eo__24from_5fclause(s, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn case_0_eo__24eo_5fprog_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24eo_5fprog_5fresolution(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24to_5fclause(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_2_eo__24eo_5fprog_5fresolution(s, v9, v1, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_3_eo__24eo_5fprog_5fresolution(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24to_5fclause(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Eq, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match if_5_eo__24eo_5fprog_5fresolution(s, v22, v3, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_list(EvalOp::ListConcat, &[v4, v17, v30]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fresolution(s, v31)
}
pub(super) fn body_eo__24eo_5fprog_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fresolution(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_resolution"
pub fn eo__24eo_5fprog_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fresolution(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v12: Term, v2: Term, v5: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24eo_5fpf, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24eo_5fprog_5fresolution(s, v2, v5, v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_3_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eresolution, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = fields[1];
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fpf, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v12, v2, v5, v16)
}
pub(super) fn cases_0_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fmk_5fpremise_5flist(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5fnil(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
// EO program "$eo_mk_premise_list"
pub fn eo__24eo_5fmk_5fpremise_5flist(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fmk_5fpremise_5flist(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn body_eo__24eo_5fmk_5fpremise_5flist(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fmk_5fpremise_5flist(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fmk_5fpremise_5flist(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fmk_5fpremise_5flist(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fstate_5fproven_5fnth(s, a2, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fmk_5fpremise_5flist(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::Cons, &[a0, v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24eo_5fprog_5fchain_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24chain_5fm_5fresolve(s, v1, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24from_5fclause(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fprog_5fchain_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fchain_5fresolution(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_chain_resolution"
pub fn eo__24eo_5fprog_5fchain_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fchain_5fresolution(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2echain_5fresolution, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fmk_5fpremise_5flist(s, v8, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fprog_5fchain_5fresolution(s, v2, v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn if_0_eo__24eo_5fprog_5fchain_5fm_5fresolution(s: &mut Store, condition: Term, v1: Term, a1: Term, a2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24chain_5fm_5fresolve(s, v1, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_list(EvalOp::ListSetof, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListMinclude, &[v8, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24eo_5fprog_5fchain_5fm_5fresolution(s: &mut Store, v13: Term, v14: Term, a0: Term) -> CheckResult<Term> {
if v13 != v14 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v13) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fchain_5fm_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24chain_5fm_5fresolve(s, v1, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_list(EvalOp::ListSetof, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24from_5fclause(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Eq, &[v5, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_0_eo__24eo_5fprog_5fchain_5fm_5fresolution(s, v6, v1, a1, a2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match requires_1_eo__24eo_5fprog_5fchain_5fm_5fresolution(s, v13, v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn body_eo__24eo_5fprog_5fchain_5fm_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fchain_5fm_5fresolution(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_chain_m_resolution"
pub fn eo__24eo_5fprog_5fchain_5fm_5fresolution(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fchain_5fm_5fresolution(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_5_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2echain_5fm_5fresolution, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v7 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = fields[1];
let v10 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fmk_5fpremise_5flist(s, v11, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fprog_5fchain_5fm_5fresolution(s, v2, v5, v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5ffactoring(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_list(EvalOp::ListSetof, &[v2, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24from_5fclause(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5fprog_5ffactoring(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5ffactoring(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_factoring"
pub fn eo__24eo_5fprog_5ffactoring(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5ffactoring(s, a0);
s.leave();
result
}
pub(super) fn case_6_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2efactoring, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5ffactoring(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn requires_0_eo__24eo_5fprog_5freordering(s: &mut Store, v3: Term, v4: Term, a0: Term) -> CheckResult<Term> {
if v3 != v4 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5freordering(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_list(EvalOp::ListMinclude, &[v2, a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match requires_0_eo__24eo_5fprog_5freordering(s, v3, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fprog_5freordering(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5freordering(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_reordering"
pub fn eo__24eo_5fprog_5freordering(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5freordering(s, a0, a1);
s.leave();
result
}
pub(super) fn case_7_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ereordering, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fprog_5freordering(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn cases_0_1_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5feq_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
if v9 != v1 { return Ok(None); }
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5feq_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5feq_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_eq_resolve"
pub fn eo__24eo_5fprog_5feq_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5feq_5fresolve(s, a0, a1);
s.leave();
result
}
pub(super) fn more_1_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match eo__24eo_5fprog_5feq_5fresolve(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_8_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eeq_5fresolve, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fpf, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fcmd_5fstep_5fproven(s, v10, v12)
}
pub(super) fn case_0_eo__24eo_5fprog_5fmodus_5fponens(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
if v9 != v1 { return Ok(None); }
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fmodus_5fponens(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fmodus_5fponens(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_modus_ponens"
pub fn eo__24eo_5fprog_5fmodus_5fponens(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fmodus_5fponens(s, a0, a1);
s.leave();
result
}
pub(super) fn more_2_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match eo__24eo_5fprog_5fmodus_5fponens(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_9_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2emodus_5fponens, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fpf, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fcmd_5fstep_5fproven(s, v10, v12)
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fnot_5felim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fnot_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fnot_5felim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_not_elim"
pub fn eo__24eo_5fprog_5fnot_5fnot_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fnot_5felim(s, a0);
s.leave();
result
}
pub(super) fn case_10_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fnot_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fnot_5felim(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcontra(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
if v6 != v1 { return Ok(None); }
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fcontra(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fcontra(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_contra"
pub fn eo__24eo_5fprog_5fcontra(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcontra(s, a0, a1);
s.leave();
result
}
pub(super) fn more_3_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match eo__24eo_5fprog_5fcontra(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_11_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econtra, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fpf, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fcmd_5fstep_5fproven(s, v10, v12)
}
pub(super) fn cases_0_2_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fand_5felim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_list(EvalOp::ListNth, &[v2, v1, a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fprog_5fand_5felim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fand_5felim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_and_elim"
pub fn eo__24eo_5fprog_5fand_5felim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fand_5felim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_12_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eand_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fprog_5fand_5felim(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_0_eo__24eo_5fprog_5fand_5fintro(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fprog_5fand_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fand_5fintro(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_and_intro"
pub fn eo__24eo_5fprog_5fand_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fand_5fintro(s, a0);
s.leave();
result
}
pub(super) fn case_13_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eand_5fintro, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fmk_5fpremise_5flist(s, v2, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fpf, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fprog_5fand_5fintro(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5for_5felim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListNth, &[v7, v4, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5for_5felim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5for_5felim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_or_elim"
pub fn eo__24eo_5fprog_5fnot_5for_5felim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5for_5felim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_14_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5for_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fprog_5fnot_5for_5felim(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_0_eo__24eo_5fprog_5fimplies_5felim(s: &mut Store, v14: Term, v15: Term, v12: Term) -> CheckResult<Option<Term>> {
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_0_eo__24eo_5fprog_5fimplies_5felim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fimplies_5felim(s, v14, v15, v12)
}
pub(super) fn body_eo__24eo_5fprog_5fimplies_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fimplies_5felim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_implies_elim"
pub fn eo__24eo_5fprog_5fimplies_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fimplies_5felim(s, a0);
s.leave();
result
}
pub(super) fn case_15_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eimplies_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fimplies_5felim(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_3_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fimplies_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_implies_elim1"
pub fn eo__24eo_5fprog_5fnot_5fimplies_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fimplies_5felim1(s, a0);
s.leave();
result
}
pub(super) fn case_16_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fimplies_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fimplies_5felim1(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fimplies_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_implies_elim2"
pub fn eo__24eo_5fprog_5fnot_5fimplies_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fimplies_5felim2(s, a0);
s.leave();
result
}
pub(super) fn case_17_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fimplies_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fimplies_5felim2(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fequiv_5felim1(s: &mut Store, v14: Term, v15: Term, v12: Term) -> CheckResult<Option<Term>> {
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_0_eo__24eo_5fprog_5fequiv_5felim1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fequiv_5felim1(s, v14, v15, v12)
}
pub(super) fn body_eo__24eo_5fprog_5fequiv_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fequiv_5felim1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_equiv_elim1"
pub fn eo__24eo_5fprog_5fequiv_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fequiv_5felim1(s, a0);
s.leave();
result
}
pub(super) fn case_18_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eequiv_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fequiv_5felim1(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fequiv_5felim2(s: &mut Store, v14: Term, v15: Term, v10: Term) -> CheckResult<Option<Term>> {
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v10, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_0_eo__24eo_5fprog_5fequiv_5felim2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fequiv_5felim2(s, v14, v15, v10)
}
pub(super) fn body_eo__24eo_5fprog_5fequiv_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fequiv_5felim2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_equiv_elim2"
pub fn eo__24eo_5fprog_5fequiv_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fequiv_5felim2(s, a0);
s.leave();
result
}
pub(super) fn case_19_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eequiv_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fequiv_5felim2(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_4_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1(s: &mut Store, v16: Term, v14: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1(s, v16, v14)
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fequiv_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_equiv_elim1"
pub fn eo__24eo_5fprog_5fnot_5fequiv_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fequiv_5felim1(s, a0);
s.leave();
result
}
pub(super) fn case_20_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fequiv_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fequiv_5felim1(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2(s: &mut Store, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2(s, v8, v16)
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fequiv_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_equiv_elim2"
pub fn eo__24eo_5fprog_5fnot_5fequiv_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fequiv_5felim2(s, a0);
s.leave();
result
}
pub(super) fn case_21_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fequiv_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fequiv_5felim2(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5fxor_5felim1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn body_eo__24eo_5fprog_5fxor_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fxor_5felim1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_xor_elim1"
pub fn eo__24eo_5fprog_5fxor_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fxor_5felim1(s, a0);
s.leave();
result
}
pub(super) fn case_22_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2exor_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fxor_5felim1(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fxor_5felim2(s: &mut Store, v13: Term, v15: Term, v12: Term) -> CheckResult<Option<Term>> {
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5fxor_5felim2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fxor_5felim2(s, v13, v15, v12)
}
pub(super) fn body_eo__24eo_5fprog_5fxor_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fxor_5felim2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_xor_elim2"
pub fn eo__24eo_5fprog_5fxor_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fxor_5felim2(s, a0);
s.leave();
result
}
pub(super) fn case_23_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2exor_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fxor_5felim2(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_5_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_20_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_21_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_22_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_23_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fnot_5fxor_5felim1(s: &mut Store, v16: Term, v8: Term, v15: Term, v14: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v16, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fnot_5fxor_5felim1(s, v16, v8, v15, v14)
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fxor_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_xor_elim1"
pub fn eo__24eo_5fprog_5fnot_5fxor_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fxor_5felim1(s, a0);
s.leave();
result
}
pub(super) fn case_24_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fxor_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fxor_5felim1(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fnot_5fxor_5felim2(s: &mut Store, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v16, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fnot_5fxor_5felim2(s, v8, v16)
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fxor_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_xor_elim2"
pub fn eo__24eo_5fprog_5fnot_5fxor_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fxor_5felim2(s, a0);
s.leave();
result
}
pub(super) fn case_25_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fxor_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fxor_5felim2(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_5felim1(s: &mut Store, v17: Term, v15: Term) -> CheckResult<Option<Term>> {
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_5felim1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v7) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_5felim1(s, v17, v15)
}
pub(super) fn body_eo__24eo_5fprog_5fite_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_5felim1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite_elim1"
pub fn eo__24eo_5fprog_5fite_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_5felim1(s, a0);
s.leave();
result
}
pub(super) fn case_26_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fite_5felim1(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_5felim2(s: &mut Store, v13: Term, v17: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_5felim2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_5felim2(s, v13, v17)
}
pub(super) fn body_eo__24eo_5fprog_5fite_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_5felim2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite_elim2"
pub fn eo__24eo_5fprog_5fite_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_5felim2(s, a0);
s.leave();
result
}
pub(super) fn case_27_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fite_5felim2(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_6_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_24_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_25_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_26_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_27_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fnot_5fite_5felim1(s: &mut Store, v16: Term, v18: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fite_5felim1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v14) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fnot_5fite_5felim1(s, v16, v18, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fite_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fite_5felim1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_ite_elim1"
pub fn eo__24eo_5fprog_5fnot_5fite_5felim1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fite_5felim1(s, a0);
s.leave();
result
}
pub(super) fn case_28_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fite_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fite_5felim1(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fnot_5fite_5felim2(s: &mut Store, v8: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fite_5felim2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fnot_5fite_5felim2(s, v8, v18, v17)
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fite_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fite_5felim2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_ite_elim2"
pub fn eo__24eo_5fprog_5fnot_5fite_5felim2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fite_5felim2(s, a0);
s.leave();
result
}
pub(super) fn case_29_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fite_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fite_5felim2(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24lower_5fnot_5fand(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$lower_not_and"
pub fn eo__24lower_5fnot_5fand(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(905), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24lower_5fnot_5fand(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(905), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24lower_5fnot_5fand(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24lower_5fnot_5fand(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24lower_5fnot_5fand(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24lower_5fnot_5fand(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24lower_5fnot_5fand(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnot_5fand(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match eo__24lower_5fnot_5fand(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fnot_5fand(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fnot_5fand(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_not_and"
pub fn eo__24eo_5fprog_5fnot_5fand(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnot_5fand(s, a0);
s.leave();
result
}
pub(super) fn case_30_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enot_5fand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnot_5fand(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fand_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_list(EvalOp::ListNth, &[v5, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v3, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fand_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fand_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_and_pos"
pub fn eo__24eo_5fprog_5fcnf_5fand_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fand_5fpos(s, a0, a1);
s.leave();
result
}
pub(super) fn case_31_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fand_5fpos, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fcnf_5fand_5fpos(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_7_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_28_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_29_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_30_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_31_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_6_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_7_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fand_5fneg(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24lower_5fnot_5fand(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fand_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fand_5fneg(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_and_neg"
pub fn eo__24eo_5fprog_5fcnf_5fand_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fand_5fneg(s, a0);
s.leave();
result
}
pub(super) fn case_32_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fand_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fand_5fneg(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5for_5fpos(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5for_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5for_5fpos(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_or_pos"
pub fn eo__24eo_5fprog_5fcnf_5for_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5for_5fpos(s, a0);
s.leave();
result
}
pub(super) fn case_33_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5for_5fpos, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5for_5fpos(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5for_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListNth, &[v4, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v1, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5for_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5for_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_or_neg"
pub fn eo__24eo_5fprog_5fcnf_5for_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5for_5fneg(s, a0, a1);
s.leave();
result
}
