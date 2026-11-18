//! Generated functions, module 2 of 12.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v10, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fite_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_ite_pos2"
pub fn eo__24eo_5fprog_5fcnf_5fite_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fite_5fpos2(s, a0);
s.leave();
result
}
pub(super) fn case_47_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fite_5fpos2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fite_5fpos2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_5_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_40_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_41_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_42_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_43_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_44_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_45_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_46_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_47_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v10, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fite_5fpos3(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_ite_pos3"
pub fn eo__24eo_5fprog_5fcnf_5fite_5fpos3(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fite_5fpos3(s, a0);
s.leave();
result
}
pub(super) fn case_48_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fite_5fpos3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fite_5fpos3(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v15, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fite_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_ite_neg1"
pub fn eo__24eo_5fprog_5fcnf_5fite_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fite_5fneg1(s, a0);
s.leave();
result
}
pub(super) fn case_49_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fite_5fneg1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fite_5fneg1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v15, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fite_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_ite_neg2"
pub fn eo__24eo_5fprog_5fcnf_5fite_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fite_5fneg2(s, a0);
s.leave();
result
}
pub(super) fn case_50_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fite_5fneg2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fite_5fneg2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v15, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fite_5fneg3(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_ite_neg3"
pub fn eo__24eo_5fprog_5fcnf_5fite_5fneg3(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fite_5fneg3(s, a0);
s.leave();
result
}
pub(super) fn case_51_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fite_5fneg3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fite_5fneg3(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s: &mut Store, v34: Term, v9: Term, v31: Term, v2: Term, v30: Term, v15: Term) -> CheckResult<Option<Term>> {
let v35 = match s.apply(v34, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v31, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v30, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v38, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.unapply(v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != v12 { return Ok(None); }
if v25 != v2 { return Ok(None); }
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s, v34, v9, v31, v2, v30, v15)
}
pub(super) fn body_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arrays_read_over_write"
pub fn eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s, a0, a1);
s.leave();
result
}
pub(super) fn case_52_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earrays_5fread_5fover_5fwrite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s: &mut Store, v37: Term, v15: Term, v25: Term) -> CheckResult<Option<Term>> {
let v38 = match s.apply(v37, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn case_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.unapply(v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
let v30 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
let v36 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != v28 { return Ok(None); }
if v32 != v15 { return Ok(None); }
let v37 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s, v37, v15, v25)
}
pub(super) fn body_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arrays_read_over_write_contra"
pub fn eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s, a0);
s.leave();
result
}
pub(super) fn case_53_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
if v2 != v12 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn body_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arrays_read_over_write_1"
pub fn eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s, a0);
s.leave();
result
}
pub(super) fn case_54_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5farrays_5fext(s: &mut Store, v13: Term, v28: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v13, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn case_0_eo__24eo_5fprog_5farrays_5fext(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__40array_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__40array_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v21, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farrays_5fext(s, v13, v28)
}
pub(super) fn body_eo__24eo_5fprog_5farrays_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5farrays_5fext(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arrays_ext"
pub fn eo__24eo_5fprog_5farrays_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farrays_5fext(s, a0);
s.leave();
result
}
pub(super) fn case_55_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earrays_5fext, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5farrays_5fext(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_6_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_48_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_49_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_50_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_51_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_52_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_53_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_54_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_55_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5frefl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fprog_5frefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5frefl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_refl"
pub fn eo__24eo_5fprog_5frefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5frefl(s, a0);
s.leave();
result
}
pub(super) fn case_56_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2erefl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5frefl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24mk_5fsymm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_1_eo__24mk_5fsymm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn body_eo__24mk_5fsymm(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fsymm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fsymm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_symm"
pub fn eo__24mk_5fsymm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fsymm(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fsymm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24mk_5fsymm(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fprog_5fsymm(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fsymm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_symm"
pub fn eo__24eo_5fprog_5fsymm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsymm(s, a0);
s.leave();
result
}
pub(super) fn case_57_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esymm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fsymm(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24mk_5ftrans(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$mk_trans"
pub fn eo__24mk_5ftrans(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(937), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5ftrans(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(937), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5ftrans(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5ftrans(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5ftrans(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5ftrans(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v15 = match requires_0_eo__24mk_5ftrans(s, a1, v12, a0, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn requires_0_eo__24mk_5ftrans(s: &mut Store, a1: Term, v12: Term, a0: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if a1 != v12 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v14 = match eo__24mk_5ftrans(s, a0, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
pub(super) fn case_0_eo__24eo_5fprog_5ftrans(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match eo__24mk_5ftrans(s, v14, v11, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn body_eo__24eo_5fprog_5ftrans(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5ftrans(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_trans"
pub fn eo__24eo_5fprog_5ftrans(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5ftrans(s, a0);
s.leave();
result
}
pub(super) fn case_58_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2etrans, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fmk_5fpremise_5flist(s, v2, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fpf, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fprog_5ftrans(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_1_eo__24mk_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(a0))
}
// EO program "$mk_cong_rhs"
pub fn eo__24mk_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(914), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fcong_5frhs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(914), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fcong_5frhs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fcong_5frhs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
if v15 != v2 { return Ok(None); }
let v17 = match eo__24mk_5fcong_5frhs(s, v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListRev, &[v4, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24mk_5fcong_5frhs(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcong(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cong"
pub fn eo__24eo_5fprog_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcong(s, a0, a1);
s.leave();
result
}
pub(super) fn case_59_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fmk_5fpremise_5flist(s, v5, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fcong(s, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24mk_5fnary_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(a0))
}
// EO program "$mk_nary_cong_rhs"
pub fn eo__24mk_5fnary_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(925), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fnary_5fcong_5frhs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(925), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fnary_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fnary_5fcong_5frhs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fnary_5fcong_5frhs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5fnary_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
if v18 != v5 { return Ok(None); }
let v20 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24mk_5fnary_5fcong_5frhs(s, v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24eo_5fprog_5fnary_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24mk_5fnary_5fcong_5frhs(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fprog_5fnary_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fnary_5fcong(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_nary_cong"
pub fn eo__24eo_5fprog_5fnary_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fnary_5fcong(s, a0, a1);
s.leave();
result
}
pub(super) fn case_60_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2enary_5fcong, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fmk_5fpremise_5flist(s, v5, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fnary_5fcong(s, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5fpairwise_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24mk_5fnary_5fcong_5frhs(s, v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fpairwise_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fpairwise_5fcong(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_pairwise_cong"
pub fn eo__24eo_5fprog_5fpairwise_5fcong(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fpairwise_5fcong(s, a0, a1);
s.leave();
result
}
pub(super) fn case_61_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2epairwise_5fcong, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fmk_5fpremise_5flist(s, v5, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fpairwise_5fcong(s, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5ftrue_5fintro(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fprog_5ftrue_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5ftrue_5fintro(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_true_intro"
pub fn eo__24eo_5fprog_5ftrue_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5ftrue_5fintro(s, a0);
s.leave();
result
}
pub(super) fn case_62_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2etrue_5fintro, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5ftrue_5fintro(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5ftrue_5felim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5ftrue_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5ftrue_5felim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_true_elim"
pub fn eo__24eo_5fprog_5ftrue_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5ftrue_5felim(s, a0);
s.leave();
result
}
pub(super) fn case_63_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2etrue_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5ftrue_5felim(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_7_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_56_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_57_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_58_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_59_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_60_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_61_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_62_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_63_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5ffalse_5fintro(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5ffalse_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5ffalse_5fintro(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_false_intro"
pub fn eo__24eo_5fprog_5ffalse_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5ffalse_5fintro(s, a0);
s.leave();
result
}
pub(super) fn case_64_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2efalse_5fintro, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5ffalse_5fintro(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5ffalse_5felim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5ffalse_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5ffalse_5felim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_false_elim"
pub fn eo__24eo_5fprog_5ffalse_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5ffalse_5felim(s, a0);
s.leave();
result
}
pub(super) fn case_65_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2efalse_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5ffalse_5felim(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24mk_5fho_5fcong(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.apply(a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(a1, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v14, v15, v2])))
}
pub(super) fn case_1_eo__24mk_5fho_5fcong(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn step_eo__24mk_5fho_5fcong(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24mk_5fho_5fcong(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fho_5fcong(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24mk_5fho_5fcong(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24mk_5fho_5fcong(s, a0, a1, a2) {
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
// EO program "$mk_ho_cong"
pub fn eo__24mk_5fho_5fcong(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(924), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fho_5fcong(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(924), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fho_5fcong(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match eo__24mk_5fho_5fcong(s, v14, v11, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn body_eo__24eo_5fprog_5fho_5fcong(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fho_5fcong(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ho_cong"
pub fn eo__24eo_5fprog_5fho_5fcong(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fho_5fcong(s, a0);
s.leave();
result
}
pub(super) fn case_66_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eho_5fcong, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fmk_5fpremise_5flist(s, v2, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fpf, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fprog_5fho_5fcong(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdistinct_2delim(s: &mut Store, v9: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v9 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
pub(super) fn case_1_eo__24mk_5fdistinct_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
Ok(Some(a2))
}
// EO program "$mk_distinct_elim_rec"
pub fn eo__24mk_5fdistinct_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(916), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdistinct_5felim_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(916), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fdistinct_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdistinct_5felim_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdistinct_5felim_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5fdistinct_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24mk_5fdistinct_5felim_5frec(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_1_eo__24mk_5fdistinct_5felim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$mk_distinct_elim"
pub fn eo__24mk_5fdistinct_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(915), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdistinct_5felim(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(915), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fdistinct_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdistinct_5felim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdistinct_5felim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5fdistinct_5felim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24mk_5fdistinct_5felim(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24mk_5fdistinct_5felim_5frec(s, v9, v6, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdistinct_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24mk_5fdistinct_5felim(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListSingletonElim, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match requires_0_eo__24eo_5fprog_5fdistinct_2delim(s, v9, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24eo_5fprog_5fdistinct_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdistinct_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_distinct-elim"
pub fn eo__24eo_5fprog_5fdistinct_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdistinct_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_67_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edistinct_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdistinct_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdistinct_2dtrue(s: &mut Store, v14: Term, v15: Term, v9: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
pub(super) fn case_0_eo__24typed_5flist_5felement_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24typed_5flist_5felement_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24typed_5flist_5felement_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$typed_list_element_type"
pub fn eo__24typed_5flist_5felement_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24typed_5flist_5felement_5ftype(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fdistinct_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v11 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v11 { return Ok(None); }
let v12 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24typed_5flist_5felement_5ftype(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24are_5fdistinct_5fterms_5flist(s, v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match requires_0_eo__24eo_5fprog_5fdistinct_2dtrue(s, v14, v15, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn body_eo__24eo_5fprog_5fdistinct_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdistinct_2dtrue(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_distinct-true"
pub fn eo__24eo_5fprog_5fdistinct_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdistinct_2dtrue(s, a0);
s.leave();
result
}
pub(super) fn case_68_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edistinct_5ftrue, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdistinct_2dtrue(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdistinct_2dfalse(s: &mut Store, v14: Term, v15: Term, v9: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
pub(super) fn case_0_eo__24eo_5fprog_5fdistinct_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v11 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSetof, &[v12, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[v13, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match requires_0_eo__24eo_5fprog_5fdistinct_2dfalse(s, v14, v15, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn body_eo__24eo_5fprog_5fdistinct_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdistinct_2dfalse(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_distinct-false"
pub fn eo__24eo_5fprog_5fdistinct_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdistinct_2dfalse(s, a0);
s.leave();
result
}
pub(super) fn case_69_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edistinct_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdistinct_2dfalse(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24mk_5farith_5fsum_5fub_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(Next::Done(a1)))
}
pub(super) fn case_1_eo__24mk_5farith_5fsum_5fub_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24arith_5frel_5fsum(s, v11, v17, v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v25])))
}
pub(super) fn step_eo__24mk_5farith_5fsum_5fub_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24mk_5farith_5fsum_5fub_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5farith_5fsum_5fub_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24mk_5farith_5fsum_5fub_5frec(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24mk_5farith_5fsum_5fub_5frec(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$mk_arith_sum_ub_rec"
pub fn eo__24mk_5farith_5fsum_5fub_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(912), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5farith_5fsum_5fub_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(912), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24mk_5farith_5fsum_5fub(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListRev, &[v13, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24arith_5fmk_5fzero(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24arith_5fmk_5fzero(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24mk_5farith_5fsum_5fub_5frec(s, v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn body_eo__24mk_5farith_5fsum_5fub(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5farith_5fsum_5fub(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_arith_sum_ub"
pub fn eo__24mk_5farith_5fsum_5fub(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5farith_5fsum_5fub(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fsum_5fub(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24mk_5farith_5fsum_5fub(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fsum_5fub(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fsum_5fub(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_sum_ub"
pub fn eo__24eo_5fprog_5farith_5fsum_5fub(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fsum_5fub(s, a0);
s.leave();
result
}
pub(super) fn case_70_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fsum_5fub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fmk_5fpremise_5flist(s, v2, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fpf, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fprog_5farith_5fsum_5fub(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn more_0_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fnil(s, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v7, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5fnil(s, v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
}
pub(super) fn more_1_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_1_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fnil(s, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v7, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5fnil(s, v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
}
pub(super) fn more_2_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_2_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fnil(s, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v7, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5fnil(s, v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
}
pub(super) fn more_3_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_3_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fnil(s, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v7, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5fnil(s, v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
}
pub(super) fn more_4_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_4_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fnil(s, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v7, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5fnil(s, v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
}
pub(super) fn body_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_4_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_arith_mult_pos"
pub fn eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5farith_5fmult_5fpos(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24arith_5fmk_5fzero(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v1, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_mult_pos"
pub fn eo__24eo_5fprog_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fmult_5fpos(s, a0, a1);
s.leave();
result
}
pub(super) fn case_71_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmult_5fpos, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_5fmult_5fpos(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_8_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_64_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_65_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_66_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_67_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_68_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_69_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_70_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_71_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24mk_5farith_5fmult_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5fnil(s, v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v7, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5fnil(s, v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24arith_5frel_5finv(s, v4, v14, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn body_eo__24mk_5farith_5fmult_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5farith_5fmult_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_arith_mult_neg"
pub fn eo__24mk_5farith_5fmult_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5farith_5fmult_5fneg(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fmult_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24arith_5fmk_5fzero(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v1, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24mk_5farith_5fmult_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fmult_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fmult_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_mult_neg"
pub fn eo__24eo_5fprog_5farith_5fmult_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fmult_5fneg(s, a0, a1);
s.leave();
result
}
pub(super) fn case_72_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmult_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_5fmult_5fneg(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24mk_5farith_5ftrichotomy(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
if v11 != v5 { return Ok(None); }
if v8 != v2 { return Ok(None); }
let v12 = match eo__24arith_5frel_5ftrichotomy(s, v4, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24mk_5farith_5ftrichotomy(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5farith_5ftrichotomy(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_arith_trichotomy"
pub fn eo__24mk_5farith_5ftrichotomy(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5farith_5ftrichotomy(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5ftrichotomy(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24arith_5fnormalize_5flit(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24arith_5fnormalize_5flit(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24mk_5farith_5ftrichotomy(s, v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5ftrichotomy(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5ftrichotomy(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_trichotomy"
pub fn eo__24eo_5fprog_5farith_5ftrichotomy(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5ftrichotomy(s, a0, a1);
s.leave();
result
}
pub(super) fn case_73_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5ftrichotomy, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match eo__24eo_5fprog_5farith_5ftrichotomy(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn if_0_eo__24greatest_5fint_5flt(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_core(EvalOp::Add, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24greatest_5fint_5flt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::ToRat, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::Eq, &[v0, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_0_eo__24greatest_5fint_5flt(s, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24greatest_5fint_5flt(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24greatest_5fint_5flt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$greatest_int_lt"
pub fn eo__24greatest_5fint_5flt(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24greatest_5fint_5flt(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fint_5ftight_5fub(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24greatest_5fint_5flt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24eo_5fprog_5fint_5ftight_5fub(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fint_5ftight_5fub(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_int_tight_ub"
pub fn eo__24eo_5fprog_5fint_5ftight_5fub(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fint_5ftight_5fub(s, a0);
s.leave();
result
}
pub(super) fn case_74_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eint_5ftight_5fub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fint_5ftight_5fub(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24least_5fint_5fgt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(v0)) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::Add, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24least_5fint_5fgt(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24least_5fint_5fgt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$least_int_gt"
pub fn eo__24least_5fint_5fgt(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24least_5fint_5fgt(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fint_5ftight_5flb(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24least_5fint_5fgt(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24eo_5fprog_5fint_5ftight_5flb(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fint_5ftight_5flb(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_int_tight_lb"
pub fn eo__24eo_5fprog_5fint_5ftight_5flb(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fint_5ftight_5flb(s, a0);
s.leave();
result
}
pub(super) fn case_75_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eint_5ftight_5flb, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fint_5ftight_5flb(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn if_0_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v71 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v71)
}
Some(false) => {
let v72 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v72)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v88 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v88)
}
Some(false) => {
let v89 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v89)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, v70: Term, v75: Term, v69: Term, v64: Term, a0: Term, a2: Term, a4: Term, a1: Term, a3: Term, v63: Term) -> CheckResult<Option<Term>> {
let v76 = match s.apply(v70, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v76, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v69, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v64, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v82, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match if_2_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v87, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v93, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v86, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v81, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v97, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v80, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v63, v100) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v101))
}
pub(super) fn more_4_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, v25: Term, v49: Term, v14: Term, a2: Term, a3: Term, v13: Term, v0: Term, a0: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v50 = match s.apply(v25, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v14, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match eo__24eo_5ftypeof(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24eo_5fnil(s, v56, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v55, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v53, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v51, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v13, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v0, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v65, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match if_1_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, a3) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, v70, v75, v69, v64, a0, a2, a4, a1, a3, v63)
}
pub(super) fn more_3_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a2: Term, a1: Term, a3: Term, a0: Term, v25: Term, v14: Term, v13: Term, v0: Term, a4: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5ftypeof(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5fnil(s, v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v28, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v26, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24eo_5ftypeof(s, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5fnil(s, v42, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v41, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v39, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24eo_5ftypeof(s, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match eo__24eo_5fnil(s, v37, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v36, v48) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, v25, v49, v14, a2, a3, v13, v0, a0, a4, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fnil(s, v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v5, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v3, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5ftypeof(s, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fnil(s, v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v15, v24) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a2, a1, a3, a0, v25, v14, v13, v0, a4)
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_mult_tangent"
pub fn eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_76_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmult_5ftangent, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v10 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = fields[1];
let v13 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = fields[1];
let v16 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v17 { return Ok(None); }
let v18 = match eo__24eo_5fprog_5farith_5fmult_5ftangent(s, v2, v5, v8, v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn if_0_eo__24eo_5fprog_5farith_5fmult_5fsign(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24strip_5feven_5fexponent(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
if v5 != a0 { return Ok(None); }
let v7 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
if v12 != a0 { return Ok(None); }
Ok(Some(Next::Again([a0, v9])))
}
pub(super) fn case_1_eo__24strip_5feven_5fexponent(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
Ok(Some(Next::Done(a1)))
}
pub(super) fn step_eo__24strip_5feven_5fexponent(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24strip_5feven_5fexponent(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24strip_5feven_5fexponent(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24strip_5feven_5fexponent(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24strip_5feven_5fexponent(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$strip_even_exponent"
pub fn eo__24strip_5feven_5fexponent(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1077), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24strip_5feven_5fexponent(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1077), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn requires_3_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v1: Term, v3: Term, a0: Term) -> CheckResult<Term> {
if v1 != v3 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_3_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.builtin_core(EvalOp::ToRat, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Rational(v2)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match requires_3_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v1, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$mk_arith_mult_sign_sgn"
pub fn eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(910), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(910), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
if v23 != v16 { return Ok(None); }
let v25 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v29 != v31 { return Ok(None); }
if v30 != v16 { return Ok(None); }
let v32 = match s.builtin_core(EvalOp::ToRat, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Rational(v33)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match requires_0_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v32, v34, v16, v27, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn case_1_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
if v19 != v12 { return Ok(None); }
let v21 = match s.builtin_core(EvalOp::ToRat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Rational(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match requires_1_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v21, v23, v12, v16, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_2_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
if v19 != v12 { return Ok(None); }
let v21 = match s.builtin_core(EvalOp::ToRat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Rational(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_2_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v21, v23, a0, v12, v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn requires_0_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v32: Term, v34: Term, v16: Term, v27: Term, a0: Term, v2: Term) -> CheckResult<Term> {
if v32 != v34 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v32) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v35 = match eo__24strip_5feven_5fexponent(s, v16, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, v2, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
pub(super) fn requires_1_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v21: Term, v23: Term, v12: Term, v16: Term, a0: Term, v2: Term) -> CheckResult<Term> {
if v21 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v21) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match eo__24strip_5feven_5fexponent(s, v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, v2, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn requires_2_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v21: Term, v23: Term, a0: Term, v12: Term, v16: Term, v2: Term) -> CheckResult<Term> {
if v21 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v21) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match s.builtin_core(EvalOp::Not, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24strip_5feven_5fexponent(s, v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v24, v2, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn case_0_eo__24to_5fcube(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_1_eo__24to_5fcube(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24to_5fcube(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24to_5fcube(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24to_5fcube(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24to_5fcube(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24to_5fcube(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$to_cube"
pub fn eo__24to_5fcube(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24to_5fcube(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fmult_5fsign(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24to_5fcube(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v2, v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24eo_5fprog_5farith_5fmult_5fsign(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24arith_5fmk_5fzero(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v1, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fmult_5fsign(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fmult_5fsign(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_mult_sign"
pub fn eo__24eo_5fprog_5farith_5fmult_5fsign(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fmult_5fsign(s, a0, a1);
s.leave();
result
}
pub(super) fn case_77_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmult_5fsign, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_5fmult_5fsign(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v19: Term, v23: Term, v35: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v36 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5ftypeof(s, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24eo_5fnil(s, v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v38, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListConcat, &[v36, v23, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v35, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v44])))
}
pub(super) fn case_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
let v21 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
if v25 != v11 { return Ok(None); }
let v27 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5ftypeof(s, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5fnil(s, v30, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListConcat, &[v27, v26, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v11, v34) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v19, v23, v35, v2)
}
pub(super) fn case_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v12)))
}
// EO program "$mk_arith_mult_abs_comparison_rec"
pub fn eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(907), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(907), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
let v25 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
let v29 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v33, v34)) = v32 else { return Ok(None); }
;
let v35 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v35 { return Ok(None); }
let v36 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v37, v39, v38, v23, v31, a1, v27, v2)
}
pub(super) fn requires_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v55: Term, v57: Term, v23: Term, v53: Term, v27: Term, v50: Term, v2: Term) -> CheckResult<Term> {
if v55 != v57 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v55) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v58 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24eo_5ftypeof(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24eo_5fnil(s, v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v61, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_list(EvalOp::ListConcat, &[v59, v53, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v58, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24eo_5ftypeof(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5fnil(s, v71, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v70, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_list(EvalOp::ListConcat, &[v68, v50, v74]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v67, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v2, v76) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v77)
}
pub(super) fn more_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v37: Term, v39: Term, v38: Term, v23: Term, v31: Term, a1: Term, v27: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if v37 != v39 { return Ok(None); }
let v40 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != v23 { return Ok(None); }
let v47 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v47 { return Ok(None); }
let v48 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
let v55 = match s.builtin_core(EvalOp::ToRat, &[v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Rational(v56)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match requires_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v55, v57, v23, v53, v27, v50, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v78)))
}
pub(super) fn more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, v20: Term, v31: Term, v29: Term, v2: Term) -> CheckResult<Option<Term>> {
let v32 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5ftypeof(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fnil(s, v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v31, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v2, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn case_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5ftypeof(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24eo_5fnil(s, v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v22, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v20) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, v20, v31, v29, v2)
}
pub(super) fn more_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, v20: Term, v31: Term, v29: Term, v2: Term) -> CheckResult<Option<Term>> {
let v32 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5ftypeof(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fnil(s, v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v31, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v2, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn case_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5ftypeof(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24eo_5fnil(s, v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v22, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v20) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, v20, v31, v29, v2)
}
pub(super) fn body_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_arith_mult_abs_comparison"
pub fn eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fmult_5fabs_5fcomparison(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_mult_abs_comparison"
pub fn eo__24eo_5fprog_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fmult_5fabs_5fcomparison(s, a0);
s.leave();
result
}
pub(super) fn case_78_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fmk_5fpremise_5flist(s, v2, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fpf, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fprog_5farith_5fmult_5fabs_5fcomparison(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24arith_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_reduction"
pub fn eo__24eo_5fprog_5farith_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5freduction(s, a0);
s.leave();
result
}
pub(super) fn case_79_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5freduction, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_5freduction(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_9_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_72_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_73_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_74_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_75_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_76_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_77_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_78_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_79_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm(s: &mut Store, v7: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v7 != v8 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
pub(super) fn case_0_eo__24poly_5fneg(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$poly_neg"
pub fn eo__24poly_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(946), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fneg(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(946), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24poly_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24poly_5fneg(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24poly_5fneg(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24poly_5fneg(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Neg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24poly_5fneg(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_1_eo__24poly_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn case_2_eo__24poly_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(a0))
}
// EO program "$poly_add"
pub fn eo__24poly_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(942), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fadd(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(942), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24poly_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24poly_5fadd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24poly_5fadd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24poly_5fadd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24poly_5fadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.builtin_core(EvalOp::Eq, &[v12, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match if_2_eo__24poly_5fadd(s, v28, v9, v23, v2, v16, v12, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v71))
}
pub(super) fn if_0_eo__24poly_5fadd(s: &mut Store, condition: Term, v2: Term, v16: Term, v12: Term, v9: Term, v23: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match eo__24poly_5fadd(s, v2, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::Add, &[v9, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v34, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24poly_5fadd(s, v2, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24poly_5fadd(s: &mut Store, condition: Term, v12: Term, v9: Term, v26: Term, v23: Term, v16: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v44 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v44, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v49, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match eo__24poly_5fadd(s, v2, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v48, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v56)
}
Some(false) => {
let v57 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v57, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v62, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24poly_5fadd(s, v67, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v61, v68) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v69)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24poly_5fadd(s: &mut Store, condition: Term, v9: Term, v23: Term, v2: Term, v16: Term, v12: Term, v26: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match s.builtin_core(EvalOp::Add, &[v9, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Rational(v30)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::Eq, &[v29, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_0_eo__24poly_5fadd(s, v32, v2, v16, v12, v9, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
Some(false) => {
let v43 = match s.builtin_core(EvalOp::Compare, &[v26, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match if_1_eo__24poly_5fadd(s, v43, v12, v9, v26, v23, v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24mvar_5fmul_5fmvar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(a0))
}
pub(super) fn case_2_eo__24mvar_5fmul_5fmvar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
// EO program "$mvar_mul_mvar"
pub fn eo__24mvar_5fmul_5fmvar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(939), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mvar_5fmul_5fmvar(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(939), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mvar_5fmul_5fmvar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mvar_5fmul_5fmvar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mvar_5fmul_5fmvar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24mvar_5fmul_5fmvar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mvar_5fmul_5fmvar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.builtin_core(EvalOp::Compare, &[v12, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match if_0_eo__24mvar_5fmul_5fmvar(s, v14, v5, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn if_0_eo__24mvar_5fmul_5fmvar(s: &mut Store, condition: Term, v5: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24mvar_5fmul_5fmvar(s, v2, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v16, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
Some(false) => {
let v22 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24mvar_5fmul_5fmvar(s, v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v23, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24mon_5fmul_5fmon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24mvar_5fmul_5fmvar(s, v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Mul, &[v2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn body_eo__24mon_5fmul_5fmon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mon_5fmul_5fmon(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mon_mul_mon"
pub fn eo__24mon_5fmul_5fmon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mon_5fmul_5fmon(s, a0, a1);
s.leave();
result
}
pub(super) fn case_1_eo__24poly_5fmul_5fmon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$poly_mul_mon"
pub fn eo__24poly_5fmul_5fmon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(945), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fmul_5fmon(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(945), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24poly_5fmul_5fmon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24poly_5fmul_5fmon(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24poly_5fmul_5fmon(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24poly_5fmul_5fmon(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24mon_5fmul_5fmon(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24poly_5fmul_5fmon(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24poly_5fadd(s, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_1_eo__24poly_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24poly_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$poly_mul"
pub fn eo__24poly_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(944), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fmul(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(944), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24poly_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24poly_5fmul(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24poly_5fmul(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24poly_5fmul(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24poly_5fmul(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24poly_5fmul_5fmon(s, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24poly_5fmul(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24poly_5fadd(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn if_0_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Rational(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Not, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Rational(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Not, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_6_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
Ok(Some(Next::Again([v2])))
}
pub(super) fn if_4_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Rational(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsEq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_4_eo__24get_5farith_5fpoly_5fnorm(s, v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Rational(v24)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_7_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::IsQ, &[v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match if_5_eo__24get_5farith_5fpoly_5fnorm(s, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v30)))
}
// EO program "$get_arith_poly_norm"
pub fn eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(880), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5farith_5fpoly_5fnorm(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(880), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24get_5farith_5fpoly_5fnorm(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_4_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_5_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_6_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_7_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_0_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24poly_5fneg(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_1_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24poly_5fadd(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn case_2_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24poly_5fneg(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24poly_5fadd(s, v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_3_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24poly_5fmul(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn case_4_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::IsQ, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24get_5farith_5fpoly_5fnorm(s, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_1_eo__24get_5farith_5fpoly_5fnorm(s, v15, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v42)))
}
pub(super) fn case_5_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::IsQ, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_2_eo__24get_5farith_5fpoly_5fnorm(s, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_3_eo__24get_5farith_5fpoly_5fnorm(s, v15, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v42)))
}
pub(super) fn if_1_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Rational(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::RatDiv, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24poly_5fmul_5fmon(s, v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
Some(false) => {
let v26 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v27, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Rational(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v26, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Rational(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::RatDiv, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24poly_5fmul_5fmon(s, v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
Some(false) => {
let v26 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v27, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Rational(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v26, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match requires_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm(s, v7, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_poly_norm"
pub fn eo__24eo_5fprog_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fpoly_5fnorm(s, a0);
s.leave();
result
}
pub(super) fn case_80_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fpoly_5fnorm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, v71: Term, v72: Term, v11: Term, v12: Term, v9: Term, v18: Term, v15: Term) -> CheckResult<Term> {
if v71 != v72 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v71) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v73 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v73, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v11, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v76, v78) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v79)
}
pub(super) fn case_0_eo__24is_5feq_5fmaybe_5fto_5freal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn case_1_eo__24is_5feq_5fmaybe_5fto_5freal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
if a1 != v2 { return Ok(None); }
let v4 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24is_5feq_5fmaybe_5fto_5freal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5feq_5fmaybe_5fto_5freal(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5feq_5fmaybe_5fto_5freal(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_eq_maybe_to_real"
pub fn eo__24is_5feq_5fmaybe_5fto_5freal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5feq_5fmaybe_5fto_5freal(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_1_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, v66: Term, v67: Term, v18: Term, v15: Term, v54: Term, v11: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v66 != v67 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v66) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v68 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24is_5feq_5fmaybe_5fto_5freal(s, v54, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match requires_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v71, v72, v11, v12, v9, v18, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v80)
}
pub(super) fn requires_2_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, v61: Term, v62: Term, v12: Term, v9: Term, v40: Term, v18: Term, v15: Term, v54: Term, v11: Term) -> CheckResult<Term> {
if v61 != v62 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v61) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v63 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24is_5feq_5fmaybe_5fto_5freal(s, v40, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match requires_1_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v66, v67, v18, v15, v54, v11, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v81)
}
pub(super) fn if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(v12)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsNeg, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::Eq, &[v17, v28]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(v12)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsNeg, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::Eq, &[v17, v28]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn case_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(v12)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsNeg, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::Eq, &[v17, v28]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(v12)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsNeg, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsNeg, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsNeg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::Eq, &[v17, v28]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_poly_norm_rel_consts_rel"
pub fn eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.builtin_core(EvalOp::ToRat, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Rational(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v6, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_rat("0/1") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Rational(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Eq, &[v10, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Or, &[v9, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Not, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::And, &[v15, v18]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn body_eo__24is_5fpoly_5fnorm_5frel_5fconsts(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_poly_norm_rel_consts"
pub fn eo__24is_5fpoly_5fnorm_5frel_5fconsts(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5fpoly_5fnorm_5frel_5fconsts(s, a0);
s.leave();
result
}
pub(super) fn requires_3_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, v56: Term, v58: Term, v11: Term, v33: Term, v47: Term, v12: Term, v9: Term, v40: Term, v18: Term, v15: Term, v54: Term) -> CheckResult<Term> {
if v56 != v58 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v56) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v59 = match s.apply(v11, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24is_5fpoly_5fnorm_5frel_5fconsts(s, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match requires_2_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v61, v62, v12, v9, v40, v18, v15, v54, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v82)
}
pub(super) fn more_4_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, v46: Term, v44: Term, v37: Term, v11: Term, v33: Term, v47: Term, v12: Term, v9: Term, v40: Term, v18: Term, v15: Term) -> CheckResult<Option<Term>> {
let v48 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
let v49 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
if v51 != v37 { return Ok(None); }
let v56 = match s.builtin_core(EvalOp::ToRat, &[v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Rational(v57)) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match requires_3_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v56, v58, v11, v33, v47, v12, v9, v40, v18, v15, v54) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v83))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
if v17 != v11 { return Ok(None); }
let v19 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v34 { return Ok(None); }
let v35 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
let v42 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
more_4_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v46, v44, v37, v11, v33, v47, v12, v9, v40, v18, v15)
}
pub(super) fn body_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith_poly_norm_rel"
pub fn eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, a0, a1);
s.leave();
result
}
pub(super) fn case_81_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn if_0_eo__24eo_5fprog_5fbv_2drepeat_2delim(s: &mut Store, condition: Term, v9: Term, v11: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v17 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListRepeat, &[v17, v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo_repeat, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24eo_5fprog_5fbv_2drepeat_2delim(s: &mut Store, v22: Term, v2: Term, v11: Term, v9: Term) -> CheckResult<Term> {
if v22 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_repeat, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2drepeat_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.destruct(Constructor::eo_repeat, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::IsZ, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IsNeg, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Not, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::And, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_0_eo__24eo_5fprog_5fbv_2drepeat_2delim(s, v16, v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListSingletonElim, &[v12, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match requires_1_eo__24eo_5fprog_5fbv_2drepeat_2delim(s, v22, v2, v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2drepeat_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2drepeat_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-repeat-elim"
pub fn eo__24eo_5fprog_5fbv_2drepeat_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2drepeat_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_82_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5frepeat_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2drepeat_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v368: Term, v369: Term, v12: Term) -> CheckResult<Term> {
if v368 != v369 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v368) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v370 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.literal(Lit::Numeral(v371)) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.literal(Lit::Numeral(v373)) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.literal(Lit::Numeral(v375)) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match eo__24bv_5fbitwidth(s, v377) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.literal(Lit::Numeral(v379)) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.builtin_core(EvalOp::Add, &[v378, v380]) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.builtin_core(EvalOp::Add, &[v376, v381]) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.builtin_core(EvalOp::Add, &[v374, v382]) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.literal(Lit::Numeral(v384)) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.builtin_core(EvalOp::Add, &[v383, v385]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.builtin_list(EvalOp::ListRepeat, &[v370, v372, v386]) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.literal(Lit::Numeral(v388)) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match eo__24iota_5frec(s, v387, v389) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v390)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v725: Term, v726: Term, v12: Term) -> CheckResult<Term> {
if v725 != v726 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v725) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v727 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v728 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v729 = match s.literal(Lit::Numeral(v728)) { Ok(v) => v, Err(e) => return Err(e) };
let v730 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v731 = match s.literal(Lit::Numeral(v730)) { Ok(v) => v, Err(e) => return Err(e) };
let v732 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v733 = match s.literal(Lit::Numeral(v732)) { Ok(v) => v, Err(e) => return Err(e) };
let v734 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v735 = match eo__24bv_5fbitwidth(s, v734) { Ok(v) => v, Err(e) => return Err(e) };
let v736 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v737 = match s.literal(Lit::Numeral(v736)) { Ok(v) => v, Err(e) => return Err(e) };
let v738 = match s.builtin_core(EvalOp::Add, &[v735, v737]) { Ok(v) => v, Err(e) => return Err(e) };
let v739 = match s.builtin_core(EvalOp::Add, &[v733, v738]) { Ok(v) => v, Err(e) => return Err(e) };
let v740 = match s.builtin_core(EvalOp::Add, &[v731, v739]) { Ok(v) => v, Err(e) => return Err(e) };
let v741 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v742 = match s.literal(Lit::Numeral(v741)) { Ok(v) => v, Err(e) => return Err(e) };
let v743 = match s.builtin_core(EvalOp::Add, &[v740, v742]) { Ok(v) => v, Err(e) => return Err(e) };
let v744 = match s.builtin_list(EvalOp::ListRepeat, &[v727, v729, v743]) { Ok(v) => v, Err(e) => return Err(e) };
let v745 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v746 = match s.literal(Lit::Numeral(v745)) { Ok(v) => v, Err(e) => return Err(e) };
let v747 = match eo__24iota_5frec(s, v744, v746) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v747)
}
pub(super) fn more_22_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v398: Term, v757: Term, v139: Term) -> CheckResult<Term> {
let v758 = match s.apply(v398, v757) { Ok(v) => v, Err(e) => return Err(e) };
let v759 = match s.apply(v139, v758) { Ok(v) => v, Err(e) => return Err(e) };
let v760 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v761 = match s.literal(Lit::Binary(BitVec::new(1, &v760))) { Ok(v) => v, Err(e) => return Err(e) };
let v762 = match s.apply(v759, v761) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v762)
}
pub(super) fn more_21_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v672: Term, v707: Term, v671: Term, v629: Term, v12: Term, v525: Term, v553: Term, v593: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v708 = match eo__24eo_5fnil(s, v672, v707) { Ok(v) => v, Err(e) => return Err(e) };
let v709 = match s.apply(v671, v708) { Ok(v) => v, Err(e) => return Err(e) };
let v710 = match s.apply(v629, v709) { Ok(v) => v, Err(e) => return Err(e) };
let v711 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v712 = match s.literal(Lit::Numeral(v711)) { Ok(v) => v, Err(e) => return Err(e) };
let v713 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v714 = match s.literal(Lit::Numeral(v713)) { Ok(v) => v, Err(e) => return Err(e) };
let v715 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v716 = match eo__24bv_5fbitwidth(s, v715) { Ok(v) => v, Err(e) => return Err(e) };
let v717 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v718 = match s.literal(Lit::Numeral(v717)) { Ok(v) => v, Err(e) => return Err(e) };
let v719 = match s.builtin_core(EvalOp::Add, &[v716, v718]) { Ok(v) => v, Err(e) => return Err(e) };
let v720 = match s.builtin_core(EvalOp::Add, &[v714, v719]) { Ok(v) => v, Err(e) => return Err(e) };
let v721 = match s.builtin_core(EvalOp::Add, &[v712, v720]) { Ok(v) => v, Err(e) => return Err(e) };
let v722 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v723 = match s.literal(Lit::Numeral(v722)) { Ok(v) => v, Err(e) => return Err(e) };
let v724 = match s.builtin_core(EvalOp::Add, &[v721, v723]) { Ok(v) => v, Err(e) => return Err(e) };
let v725 = match s.builtin_core(EvalOp::IsNeg, &[v724]) { Ok(v) => v, Err(e) => return Err(e) };
let v726 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v748 = match requires_1_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v725, v726, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v749 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v750 = match eo__24bv_5fbitwidth(s, v749) { Ok(v) => v, Err(e) => return Err(e) };
let v751 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v752 = match s.literal(Lit::Numeral(v751)) { Ok(v) => v, Err(e) => return Err(e) };
let v753 = match s.builtin_core(EvalOp::Add, &[v750, v752]) { Ok(v) => v, Err(e) => return Err(e) };
let v754 = match eo__24bv_5fsmulo_5felim_5frec(s, v525, v553, v593, v710, v748, v753) { Ok(v) => v, Err(e) => return Err(e) };
let v755 = match eo__24eo_5ftypeof(s, v754) { Ok(v) => v, Err(e) => return Err(e) };
let v756 = match eo__24eo_5fnil(s, v497, v755) { Ok(v) => v, Err(e) => return Err(e) };
let v757 = match s.apply(v496, v756) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v398, v757, v139)
}
pub(super) fn more_20_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v9: Term, v680: Term, v679: Term, v677: Term, v672: Term, v671: Term, v629: Term, v525: Term, v553: Term, v593: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v681 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v682 = match eo__24bv_5fbitwidth(s, v681) { Ok(v) => v, Err(e) => return Err(e) };
let v683 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v684 = match s.literal(Lit::Numeral(v683)) { Ok(v) => v, Err(e) => return Err(e) };
let v685 = match s.builtin_core(EvalOp::Add, &[v682, v684]) { Ok(v) => v, Err(e) => return Err(e) };
let v686 = match s.construct(Constructor::eo_sign_5fextend, &[v685]) { Ok(v) => v, Err(e) => return Err(e) };
let v687 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v688 = match eo__24bv_5fbitwidth(s, v687) { Ok(v) => v, Err(e) => return Err(e) };
let v689 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v690 = match s.literal(Lit::Numeral(v689)) { Ok(v) => v, Err(e) => return Err(e) };
let v691 = match s.builtin_core(EvalOp::Add, &[v688, v690]) { Ok(v) => v, Err(e) => return Err(e) };
let v692 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v693 = match eo__24bv_5fbitwidth(s, v692) { Ok(v) => v, Err(e) => return Err(e) };
let v694 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v695 = match s.literal(Lit::Numeral(v694)) { Ok(v) => v, Err(e) => return Err(e) };
let v696 = match s.builtin_core(EvalOp::Add, &[v693, v695]) { Ok(v) => v, Err(e) => return Err(e) };
let v697 = match s.construct(Constructor::eo_extract, &[v691, v696]) { Ok(v) => v, Err(e) => return Err(e) };
let v698 = match s.apply(v697, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v699 = match s.apply(v686, v698) { Ok(v) => v, Err(e) => return Err(e) };
let v700 = match s.apply(v680, v699) { Ok(v) => v, Err(e) => return Err(e) };
let v701 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v702 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v703 = match eo__24eo_5fnil(s, v701, v702) { Ok(v) => v, Err(e) => return Err(e) };
let v704 = match s.apply(v700, v703) { Ok(v) => v, Err(e) => return Err(e) };
let v705 = match s.apply(v679, v704) { Ok(v) => v, Err(e) => return Err(e) };
let v706 = match s.apply(v677, v705) { Ok(v) => v, Err(e) => return Err(e) };
let v707 = match eo__24eo_5ftypeof(s, v706) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v672, v707, v671, v629, v12, v525, v553, v593, v497, v496, v398, v139)
}
pub(super) fn more_19_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v652: Term, v12: Term, v650: Term, v644: Term, v643: Term, v641: Term, v630: Term, v9: Term, v629: Term, v525: Term, v553: Term, v593: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v653 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v654 = match s.literal(Lit::Numeral(v653)) { Ok(v) => v, Err(e) => return Err(e) };
let v655 = match s.builtin_core(EvalOp::Add, &[v652, v654]) { Ok(v) => v, Err(e) => return Err(e) };
let v656 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v657 = match eo__24bv_5fbitwidth(s, v656) { Ok(v) => v, Err(e) => return Err(e) };
let v658 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v659 = match s.literal(Lit::Numeral(v658)) { Ok(v) => v, Err(e) => return Err(e) };
let v660 = match s.builtin_core(EvalOp::Add, &[v657, v659]) { Ok(v) => v, Err(e) => return Err(e) };
let v661 = match s.construct(Constructor::eo_extract, &[v655, v660]) { Ok(v) => v, Err(e) => return Err(e) };
let v662 = match s.apply(v661, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v663 = match s.apply(v650, v662) { Ok(v) => v, Err(e) => return Err(e) };
let v664 = match s.apply(v644, v663) { Ok(v) => v, Err(e) => return Err(e) };
let v665 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v666 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v667 = match eo__24eo_5fnil(s, v665, v666) { Ok(v) => v, Err(e) => return Err(e) };
let v668 = match s.apply(v664, v667) { Ok(v) => v, Err(e) => return Err(e) };
let v669 = match s.apply(v643, v668) { Ok(v) => v, Err(e) => return Err(e) };
let v670 = match s.apply(v641, v669) { Ok(v) => v, Err(e) => return Err(e) };
let v671 = match s.apply(v630, v670) { Ok(v) => v, Err(e) => return Err(e) };
let v672 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v673 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v674 = match s.literal(Lit::Numeral(v673)) { Ok(v) => v, Err(e) => return Err(e) };
let v675 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v676 = match s.literal(Lit::Numeral(v675)) { Ok(v) => v, Err(e) => return Err(e) };
let v677 = match s.construct(Constructor::eo_extract, &[v674, v676]) { Ok(v) => v, Err(e) => return Err(e) };
let v678 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v679 = match s.apply(v678, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v680 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v9, v680, v679, v677, v672, v671, v629, v525, v553, v593, v497, v496, v398, v139)
}
pub(super) fn more_18_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v622: Term, v625: Term, v601: Term, v599: Term, v594: Term, v12: Term, v9: Term, v525: Term, v553: Term, v593: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v626 = match s.apply(v622, v625) { Ok(v) => v, Err(e) => return Err(e) };
let v627 = match s.apply(v601, v626) { Ok(v) => v, Err(e) => return Err(e) };
let v628 = match s.apply(v599, v627) { Ok(v) => v, Err(e) => return Err(e) };
let v629 = match s.apply(v594, v628) { Ok(v) => v, Err(e) => return Err(e) };
let v630 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v631 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v632 = match eo__24bv_5fbitwidth(s, v631) { Ok(v) => v, Err(e) => return Err(e) };
let v633 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v634 = match s.literal(Lit::Numeral(v633)) { Ok(v) => v, Err(e) => return Err(e) };
let v635 = match s.builtin_core(EvalOp::Add, &[v632, v634]) { Ok(v) => v, Err(e) => return Err(e) };
let v636 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v637 = match eo__24bv_5fbitwidth(s, v636) { Ok(v) => v, Err(e) => return Err(e) };
let v638 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v639 = match s.literal(Lit::Numeral(v638)) { Ok(v) => v, Err(e) => return Err(e) };
let v640 = match s.builtin_core(EvalOp::Add, &[v637, v639]) { Ok(v) => v, Err(e) => return Err(e) };
let v641 = match s.construct(Constructor::eo_extract, &[v635, v640]) { Ok(v) => v, Err(e) => return Err(e) };
let v642 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v643 = match s.apply(v642, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v644 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v645 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v646 = match eo__24bv_5fbitwidth(s, v645) { Ok(v) => v, Err(e) => return Err(e) };
let v647 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v648 = match s.literal(Lit::Numeral(v647)) { Ok(v) => v, Err(e) => return Err(e) };
let v649 = match s.builtin_core(EvalOp::Add, &[v646, v648]) { Ok(v) => v, Err(e) => return Err(e) };
let v650 = match s.construct(Constructor::eo_sign_5fextend, &[v649]) { Ok(v) => v, Err(e) => return Err(e) };
let v651 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v652 = match eo__24bv_5fbitwidth(s, v651) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v652, v12, v650, v644, v643, v641, v630, v9, v629, v525, v553, v593, v497, v496, v398, v139)
}
pub(super) fn more_17_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v596: Term, v598: Term, v9: Term, v12: Term, v594: Term, v525: Term, v553: Term, v593: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v599 = match s.construct(Constructor::eo_extract, &[v596, v598]) { Ok(v) => v, Err(e) => return Err(e) };
let v600 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v601 = match s.apply(v600, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v602 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v603 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v604 = match eo__24bv_5fbitwidth(s, v603) { Ok(v) => v, Err(e) => return Err(e) };
let v605 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v606 = match s.literal(Lit::Numeral(v605)) { Ok(v) => v, Err(e) => return Err(e) };
let v607 = match s.builtin_core(EvalOp::Add, &[v604, v606]) { Ok(v) => v, Err(e) => return Err(e) };
let v608 = match s.construct(Constructor::eo_sign_5fextend, &[v607]) { Ok(v) => v, Err(e) => return Err(e) };
let v609 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v610 = match eo__24bv_5fbitwidth(s, v609) { Ok(v) => v, Err(e) => return Err(e) };
let v611 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v612 = match s.literal(Lit::Numeral(v611)) { Ok(v) => v, Err(e) => return Err(e) };
let v613 = match s.builtin_core(EvalOp::Add, &[v610, v612]) { Ok(v) => v, Err(e) => return Err(e) };
let v614 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v615 = match eo__24bv_5fbitwidth(s, v614) { Ok(v) => v, Err(e) => return Err(e) };
let v616 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v617 = match s.literal(Lit::Numeral(v616)) { Ok(v) => v, Err(e) => return Err(e) };
let v618 = match s.builtin_core(EvalOp::Add, &[v615, v617]) { Ok(v) => v, Err(e) => return Err(e) };
let v619 = match s.construct(Constructor::eo_extract, &[v613, v618]) { Ok(v) => v, Err(e) => return Err(e) };
let v620 = match s.apply(v619, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v621 = match s.apply(v608, v620) { Ok(v) => v, Err(e) => return Err(e) };
let v622 = match s.apply(v602, v621) { Ok(v) => v, Err(e) => return Err(e) };
let v623 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v624 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v625 = match eo__24eo_5fnil(s, v623, v624) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v622, v625, v601, v599, v594, v12, v9, v525, v553, v593, v497, v496, v398, v139)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v569: Term, v12: Term, v567: Term, v566: Term, v564: Term, v9: Term, v525: Term, v553: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v570 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v571 = match s.literal(Lit::Numeral(v570)) { Ok(v) => v, Err(e) => return Err(e) };
let v572 = match s.builtin_core(EvalOp::Add, &[v569, v571]) { Ok(v) => v, Err(e) => return Err(e) };
let v573 = match s.construct(Constructor::eo_sign_5fextend, &[v572]) { Ok(v) => v, Err(e) => return Err(e) };
let v574 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v575 = match eo__24bv_5fbitwidth(s, v574) { Ok(v) => v, Err(e) => return Err(e) };
let v576 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v577 = match s.literal(Lit::Numeral(v576)) { Ok(v) => v, Err(e) => return Err(e) };
let v578 = match s.builtin_core(EvalOp::Add, &[v575, v577]) { Ok(v) => v, Err(e) => return Err(e) };
let v579 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v580 = match eo__24bv_5fbitwidth(s, v579) { Ok(v) => v, Err(e) => return Err(e) };
let v581 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v582 = match s.literal(Lit::Numeral(v581)) { Ok(v) => v, Err(e) => return Err(e) };
let v583 = match s.builtin_core(EvalOp::Add, &[v580, v582]) { Ok(v) => v, Err(e) => return Err(e) };
let v584 = match s.construct(Constructor::eo_extract, &[v578, v583]) { Ok(v) => v, Err(e) => return Err(e) };
let v585 = match s.apply(v584, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v586 = match s.apply(v573, v585) { Ok(v) => v, Err(e) => return Err(e) };
let v587 = match s.apply(v567, v586) { Ok(v) => v, Err(e) => return Err(e) };
let v588 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v589 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v590 = match eo__24eo_5fnil(s, v588, v589) { Ok(v) => v, Err(e) => return Err(e) };
let v591 = match s.apply(v587, v590) { Ok(v) => v, Err(e) => return Err(e) };
let v592 = match s.apply(v566, v591) { Ok(v) => v, Err(e) => return Err(e) };
let v593 = match s.apply(v564, v592) { Ok(v) => v, Err(e) => return Err(e) };
let v594 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v595 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v596 = match s.literal(Lit::Numeral(v595)) { Ok(v) => v, Err(e) => return Err(e) };
let v597 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v598 = match s.literal(Lit::Numeral(v597)) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v596, v598, v9, v12, v594, v525, v553, v593, v497, v496, v398, v139)
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v541: Term, v543: Term, v539: Term, v9: Term, v534: Term, v528: Term, v527: Term, v12: Term, v525: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v544 = match s.builtin_core(EvalOp::Add, &[v541, v543]) { Ok(v) => v, Err(e) => return Err(e) };
let v545 = match s.construct(Constructor::eo_extract, &[v539, v544]) { Ok(v) => v, Err(e) => return Err(e) };
let v546 = match s.apply(v545, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v547 = match s.apply(v534, v546) { Ok(v) => v, Err(e) => return Err(e) };
let v548 = match s.apply(v528, v547) { Ok(v) => v, Err(e) => return Err(e) };
let v549 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v550 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v551 = match eo__24eo_5fnil(s, v549, v550) { Ok(v) => v, Err(e) => return Err(e) };
let v552 = match s.apply(v548, v551) { Ok(v) => v, Err(e) => return Err(e) };
let v553 = match s.apply(v527, v552) { Ok(v) => v, Err(e) => return Err(e) };
let v554 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v555 = match eo__24bv_5fbitwidth(s, v554) { Ok(v) => v, Err(e) => return Err(e) };
let v556 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v557 = match s.literal(Lit::Numeral(v556)) { Ok(v) => v, Err(e) => return Err(e) };
let v558 = match s.builtin_core(EvalOp::Add, &[v555, v557]) { Ok(v) => v, Err(e) => return Err(e) };
let v559 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v560 = match eo__24bv_5fbitwidth(s, v559) { Ok(v) => v, Err(e) => return Err(e) };
let v561 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v562 = match s.literal(Lit::Numeral(v561)) { Ok(v) => v, Err(e) => return Err(e) };
let v563 = match s.builtin_core(EvalOp::Add, &[v560, v562]) { Ok(v) => v, Err(e) => return Err(e) };
let v564 = match s.construct(Constructor::eo_extract, &[v558, v563]) { Ok(v) => v, Err(e) => return Err(e) };
let v565 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v566 = match s.apply(v565, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v567 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v568 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v569 = match eo__24bv_5fbitwidth(s, v568) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v569, v12, v567, v566, v564, v9, v525, v553, v497, v496, v398, v139)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v511: Term, v516: Term, v12: Term, v506: Term, v500: Term, v499: Term, v9: Term, v497: Term, v496: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v517 = match s.construct(Constructor::eo_extract, &[v511, v516]) { Ok(v) => v, Err(e) => return Err(e) };
let v518 = match s.apply(v517, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v519 = match s.apply(v506, v518) { Ok(v) => v, Err(e) => return Err(e) };
let v520 = match s.apply(v500, v519) { Ok(v) => v, Err(e) => return Err(e) };
let v521 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v522 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v523 = match eo__24eo_5fnil(s, v521, v522) { Ok(v) => v, Err(e) => return Err(e) };
let v524 = match s.apply(v520, v523) { Ok(v) => v, Err(e) => return Err(e) };
let v525 = match s.apply(v499, v524) { Ok(v) => v, Err(e) => return Err(e) };
let v526 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v527 = match s.apply(v526, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v528 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v529 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v530 = match eo__24bv_5fbitwidth(s, v529) { Ok(v) => v, Err(e) => return Err(e) };
let v531 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v532 = match s.literal(Lit::Numeral(v531)) { Ok(v) => v, Err(e) => return Err(e) };
let v533 = match s.builtin_core(EvalOp::Add, &[v530, v532]) { Ok(v) => v, Err(e) => return Err(e) };
let v534 = match s.construct(Constructor::eo_sign_5fextend, &[v533]) { Ok(v) => v, Err(e) => return Err(e) };
let v535 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v536 = match eo__24bv_5fbitwidth(s, v535) { Ok(v) => v, Err(e) => return Err(e) };
let v537 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v538 = match s.literal(Lit::Numeral(v537)) { Ok(v) => v, Err(e) => return Err(e) };
let v539 = match s.builtin_core(EvalOp::Add, &[v536, v538]) { Ok(v) => v, Err(e) => return Err(e) };
let v540 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v541 = match eo__24bv_5fbitwidth(s, v540) { Ok(v) => v, Err(e) => return Err(e) };
let v542 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v543 = match s.literal(Lit::Numeral(v542)) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v541, v543, v539, v9, v534, v528, v527, v12, v525, v497, v496, v398, v139)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v475: Term, v489: Term, v469: Term, v464: Term, v463: Term, v428: Term, v399: Term, v12: Term, v9: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v490 = match s.apply(v475, v489) { Ok(v) => v, Err(e) => return Err(e) };
let v491 = match s.apply(v469, v490) { Ok(v) => v, Err(e) => return Err(e) };
let v492 = match eo__24eo_5ftypeof(s, v491) { Ok(v) => v, Err(e) => return Err(e) };
let v493 = match eo__24eo_5fnil(s, v464, v492) { Ok(v) => v, Err(e) => return Err(e) };
let v494 = match s.apply(v463, v493) { Ok(v) => v, Err(e) => return Err(e) };
let v495 = match s.apply(v428, v494) { Ok(v) => v, Err(e) => return Err(e) };
let v496 = match s.apply(v399, v495) { Ok(v) => v, Err(e) => return Err(e) };
let v497 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v498 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v499 = match s.apply(v498, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v500 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v501 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v502 = match eo__24bv_5fbitwidth(s, v501) { Ok(v) => v, Err(e) => return Err(e) };
let v503 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v504 = match s.literal(Lit::Numeral(v503)) { Ok(v) => v, Err(e) => return Err(e) };
let v505 = match s.builtin_core(EvalOp::Add, &[v502, v504]) { Ok(v) => v, Err(e) => return Err(e) };
let v506 = match s.construct(Constructor::eo_sign_5fextend, &[v505]) { Ok(v) => v, Err(e) => return Err(e) };
let v507 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v508 = match eo__24bv_5fbitwidth(s, v507) { Ok(v) => v, Err(e) => return Err(e) };
let v509 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v510 = match s.literal(Lit::Numeral(v509)) { Ok(v) => v, Err(e) => return Err(e) };
let v511 = match s.builtin_core(EvalOp::Add, &[v508, v510]) { Ok(v) => v, Err(e) => return Err(e) };
let v512 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v513 = match eo__24bv_5fbitwidth(s, v512) { Ok(v) => v, Err(e) => return Err(e) };
let v514 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v515 = match s.literal(Lit::Numeral(v514)) { Ok(v) => v, Err(e) => return Err(e) };
let v516 = match s.builtin_core(EvalOp::Add, &[v513, v515]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v511, v516, v12, v506, v500, v499, v9, v497, v496, v398, v139)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v429: Term, v462: Term, v12: Term, v9: Term, v428: Term, v399: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v463 = match s.apply(v429, v462) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match eo__24bv_5fbitwidth(s, v465) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match eo__24bv_5fbitwidth(s, v467) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match s.construct(Constructor::eo_extract, &[v466, v468]) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v471 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match s.literal(Lit::Numeral(v471)) { Ok(v) => v, Err(e) => return Err(e) };
let v473 = match s.construct(Constructor::eo_sign_5fextend, &[v472]) { Ok(v) => v, Err(e) => return Err(e) };
let v474 = match s.apply(v473, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v475 = match s.apply(v470, v474) { Ok(v) => v, Err(e) => return Err(e) };
let v476 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v477 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v478 = match s.literal(Lit::Numeral(v477)) { Ok(v) => v, Err(e) => return Err(e) };
let v479 = match s.construct(Constructor::eo_sign_5fextend, &[v478]) { Ok(v) => v, Err(e) => return Err(e) };
let v480 = match s.apply(v479, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v481 = match s.apply(v476, v480) { Ok(v) => v, Err(e) => return Err(e) };
let v482 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v483 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v484 = match s.literal(Lit::Numeral(v483)) { Ok(v) => v, Err(e) => return Err(e) };
let v485 = match s.construct(Constructor::eo_sign_5fextend, &[v484]) { Ok(v) => v, Err(e) => return Err(e) };
let v486 = match s.apply(v485, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v487 = match eo__24eo_5ftypeof(s, v486) { Ok(v) => v, Err(e) => return Err(e) };
let v488 = match eo__24eo_5fnil(s, v482, v487) { Ok(v) => v, Err(e) => return Err(e) };
let v489 = match s.apply(v481, v488) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v475, v489, v469, v464, v463, v428, v399, v12, v9, v398, v139)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v434: Term, v9: Term, v429: Term, v428: Term, v399: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v435 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match eo__24bv_5fbitwidth(s, v435) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.literal(Lit::Numeral(v437)) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match s.builtin_core(EvalOp::Add, &[v436, v438]) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.construct(Constructor::eo_extract, &[v434, v439]) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.literal(Lit::Numeral(v442)) { Ok(v) => v, Err(e) => return Err(e) };
let v444 = match s.construct(Constructor::eo_sign_5fextend, &[v443]) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match s.apply(v444, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match s.apply(v441, v445) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v448 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match s.literal(Lit::Numeral(v448)) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match s.construct(Constructor::eo_sign_5fextend, &[v449]) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match s.apply(v450, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match s.apply(v447, v451) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match s.literal(Lit::Numeral(v454)) { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.construct(Constructor::eo_sign_5fextend, &[v455]) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match s.apply(v456, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match eo__24eo_5ftypeof(s, v457) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match eo__24eo_5fnil(s, v453, v458) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.apply(v452, v459) { Ok(v) => v, Err(e) => return Err(e) };
let v461 = match s.apply(v446, v460) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.apply(v440, v461) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v429, v462, v12, v9, v428, v399, v398, v139)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v406: Term, v9: Term, v405: Term, v400: Term, v399: Term, v398: Term, v139: Term) -> CheckResult<Term> {
let v407 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.literal(Lit::Numeral(v407)) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.construct(Constructor::eo_sign_5fextend, &[v408]) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.apply(v409, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.apply(v406, v410) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.literal(Lit::Numeral(v413)) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.construct(Constructor::eo_sign_5fextend, &[v414]) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.apply(v415, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.apply(v412, v416) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.literal(Lit::Numeral(v419)) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.construct(Constructor::eo_sign_5fextend, &[v420]) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match s.apply(v421, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match eo__24eo_5ftypeof(s, v422) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match eo__24eo_5fnil(s, v418, v423) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match s.apply(v417, v424) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.apply(v411, v425) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.apply(v405, v426) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.apply(v400, v427) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match eo__24bv_5fbitwidth(s, v430) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.literal(Lit::Numeral(v432)) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.builtin_core(EvalOp::Add, &[v431, v433]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v434, v9, v429, v428, v399, v398, v139)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v358: Term, v357: Term, v355: Term, v12: Term, v168: Term, v196: Term, v236: Term, v353: Term, v140: Term, v9: Term, v139: Term) -> CheckResult<Term> {
let v359 = match eo__24bv_5fbitwidth(s, v358) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.literal(Lit::Numeral(v360)) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.builtin_core(EvalOp::Add, &[v359, v361]) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.builtin_core(EvalOp::Add, &[v357, v362]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.builtin_core(EvalOp::Add, &[v355, v363]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.literal(Lit::Numeral(v365)) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.builtin_core(EvalOp::Add, &[v364, v366]) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.builtin_core(EvalOp::IsNeg, &[v367]) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match requires_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v368, v369, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match eo__24bv_5fbitwidth(s, v392) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.literal(Lit::Numeral(v394)) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.builtin_core(EvalOp::Add, &[v393, v395]) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match eo__24bv_5fsmulo_5felim_5frec(s, v168, v196, v236, v353, v391, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.apply(v140, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match eo__24bv_5fbitwidth(s, v401) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match eo__24bv_5fbitwidth(s, v403) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.construct(Constructor::eo_extract, &[v402, v404]) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v406, v9, v405, v400, v399, v398, v139)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v330: Term, v12: Term, v9: Term, v329: Term, v323: Term, v322: Term, v320: Term, v315: Term, v314: Term, v272: Term, v168: Term, v196: Term, v236: Term, v140: Term, v139: Term) -> CheckResult<Term> {
let v331 = match eo__24bv_5fbitwidth(s, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.literal(Lit::Numeral(v332)) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.builtin_core(EvalOp::Add, &[v331, v333]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match eo__24bv_5fbitwidth(s, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.literal(Lit::Numeral(v337)) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.builtin_core(EvalOp::Add, &[v336, v338]) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.construct(Constructor::eo_extract, &[v334, v339]) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v340, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.apply(v329, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v323, v342) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match eo__24eo_5fnil(s, v344, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v343, v346) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.apply(v322, v347) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.apply(v320, v348) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match eo__24eo_5ftypeof(s, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match eo__24eo_5fnil(s, v315, v350) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v314, v351) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.apply(v272, v352) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.literal(Lit::Numeral(v354)) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.literal(Lit::Numeral(v356)) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v358, v357, v355, v12, v168, v196, v236, v353, v140, v9, v139)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v298: Term, v303: Term, v12: Term, v293: Term, v287: Term, v286: Term, v284: Term, v273: Term, v9: Term, v272: Term, v168: Term, v196: Term, v236: Term, v140: Term, v139: Term) -> CheckResult<Term> {
let v304 = match s.construct(Constructor::eo_extract, &[v298, v303]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.apply(v304, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v293, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v287, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match eo__24eo_5fnil(s, v308, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v307, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v286, v311) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.apply(v284, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v273, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.literal(Lit::Numeral(v316)) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.literal(Lit::Numeral(v318)) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo_extract, &[v317, v319]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v321, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match eo__24bv_5fbitwidth(s, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.literal(Lit::Numeral(v326)) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.builtin_core(EvalOp::Add, &[v325, v327]) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.construct(Constructor::eo_sign_5fextend, &[v328]) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v330, v12, v9, v329, v323, v322, v320, v315, v314, v272, v168, v196, v236, v140, v139)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v274: Term, v12: Term, v273: Term, v9: Term, v272: Term, v168: Term, v196: Term, v236: Term, v140: Term, v139: Term) -> CheckResult<Term> {
let v275 = match eo__24bv_5fbitwidth(s, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.literal(Lit::Numeral(v276)) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.builtin_core(EvalOp::Add, &[v275, v277]) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match eo__24bv_5fbitwidth(s, v279) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.literal(Lit::Numeral(v281)) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.builtin_core(EvalOp::Add, &[v280, v282]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_extract, &[v278, v283]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v285, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match eo__24bv_5fbitwidth(s, v288) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.literal(Lit::Numeral(v290)) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.builtin_core(EvalOp::Add, &[v289, v291]) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.construct(Constructor::eo_sign_5fextend, &[v292]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match eo__24bv_5fbitwidth(s, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.literal(Lit::Numeral(v296)) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.builtin_core(EvalOp::Add, &[v295, v297]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match eo__24bv_5fbitwidth(s, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.literal(Lit::Numeral(v301)) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.builtin_core(EvalOp::Add, &[v300, v302]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v298, v303, v12, v293, v287, v286, v284, v273, v9, v272, v168, v196, v236, v140, v139)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v247: Term, v12: Term, v9: Term, v245: Term, v244: Term, v242: Term, v237: Term, v168: Term, v196: Term, v236: Term, v140: Term, v139: Term) -> CheckResult<Term> {
let v248 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.literal(Lit::Numeral(v248)) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.builtin_core(EvalOp::Add, &[v247, v249]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.construct(Constructor::eo_sign_5fextend, &[v250]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match eo__24bv_5fbitwidth(s, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Numeral(v254)) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.builtin_core(EvalOp::Add, &[v253, v255]) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match eo__24bv_5fbitwidth(s, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.literal(Lit::Numeral(v259)) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.builtin_core(EvalOp::Add, &[v258, v260]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.construct(Constructor::eo_extract, &[v256, v261]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v262, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v251, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v245, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match eo__24eo_5fnil(s, v266, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v265, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v244, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v242, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v237, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v274, v12, v273, v9, v272, v168, v196, v236, v140, v139)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v218: Term, v220: Term, v12: Term, v216: Term, v210: Term, v209: Term, v207: Term, v9: Term, v168: Term, v196: Term, v140: Term, v139: Term) -> CheckResult<Term> {
let v221 = match s.builtin_core(EvalOp::Add, &[v218, v220]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match eo__24bv_5fbitwidth(s, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.literal(Lit::Numeral(v224)) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_core(EvalOp::Add, &[v223, v225]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_extract, &[v221, v226]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v227, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v216, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v210, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match eo__24eo_5fnil(s, v231, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v230, v233) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v209, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v207, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.literal(Lit::Numeral(v238)) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.literal(Lit::Numeral(v240)) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_extract, &[v239, v241]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v243, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match eo__24bv_5fbitwidth(s, v246) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v247, v12, v9, v245, v244, v242, v237, v168, v196, v236, v140, v139)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v9: Term, v192: Term, v191: Term, v170: Term, v12: Term, v168: Term, v140: Term, v139: Term) -> CheckResult<Term> {
let v193 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match eo__24eo_5fnil(s, v192, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v191, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v170, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match eo__24bv_5fbitwidth(s, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.literal(Lit::Numeral(v199)) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.builtin_core(EvalOp::Add, &[v198, v200]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match eo__24bv_5fbitwidth(s, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.literal(Lit::Numeral(v204)) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.builtin_core(EvalOp::Add, &[v203, v205]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_extract, &[v201, v206]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v208, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match eo__24bv_5fbitwidth(s, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.literal(Lit::Numeral(v213)) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.builtin_core(EvalOp::Add, &[v212, v214]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo_sign_5fextend, &[v215]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match eo__24bv_5fbitwidth(s, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.literal(Lit::Numeral(v219)) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v218, v220, v12, v216, v210, v209, v207, v9, v168, v196, v140, v139)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v164: Term, v165: Term, v163: Term, v142: Term, v9: Term, v12: Term, v140: Term, v139: Term) -> CheckResult<Term> {
let v166 = match eo__24eo_5fnil(s, v164, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v163, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v142, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v169, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match eo__24bv_5fbitwidth(s, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.literal(Lit::Numeral(v174)) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.builtin_core(EvalOp::Add, &[v173, v175]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo_sign_5fextend, &[v176]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match eo__24bv_5fbitwidth(s, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.literal(Lit::Numeral(v180)) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.builtin_core(EvalOp::Add, &[v179, v181]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match eo__24bv_5fbitwidth(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.literal(Lit::Numeral(v185)) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.builtin_core(EvalOp::Add, &[v184, v186]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_extract, &[v182, v187]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v188, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v177, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v171, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v9, v192, v191, v170, v12, v168, v140, v139)
}
pub(super) fn more_25_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v115: Term, v119: Term, v12: Term, v114: Term, v108: Term, v103: Term, v102: Term, v67: Term, v38: Term) -> CheckResult<Term> {
let v120 = match s.apply(v115, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_sign_5fextend, &[v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24eo_5ftypeof(s, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24eo_5fnil(s, v121, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v120, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v114, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v108, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match eo__24eo_5ftypeof(s, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match eo__24eo_5fnil(s, v103, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v102, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v67, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v38, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.literal(Lit::Binary(BitVec::new(1, &v136))) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v135, v137) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v138)
}
pub(super) fn more_24_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v92: Term, v91: Term, v85: Term, v79: Term, v68: Term, v9: Term, v67: Term, v38: Term) -> CheckResult<Term> {
let v93 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(v93)) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_sign_5fextend, &[v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match eo__24eo_5ftypeof(s, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match eo__24eo_5fnil(s, v92, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v91, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v85, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v79, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v68, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match eo__24bv_5fbitwidth(s, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24bv_5fbitwidth(s, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_extract, &[v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.literal(Lit::Numeral(v110)) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_sign_5fextend, &[v111]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v112, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v109, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.literal(Lit::Numeral(v116)) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_sign_5fextend, &[v117]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v118, v9) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v115, v119, v12, v114, v108, v103, v102, v67, v38)
}
pub(super) fn more_23_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v50: Term, v64: Term, v44: Term, v39: Term, v12: Term, v9: Term, v38: Term) -> CheckResult<Term> {
let v65 = match s.apply(v50, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v44, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v39, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match eo__24bv_5fbitwidth(s, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Numeral(v71)) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.builtin_core(EvalOp::Add, &[v70, v72]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match eo__24bv_5fbitwidth(s, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(v76)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_core(EvalOp::Add, &[v75, v77]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_extract, &[v73, v78]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Numeral(v81)) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_sign_5fextend, &[v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v80, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(v87)) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_sign_5fextend, &[v88]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v86, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v92, v91, v85, v79, v68, v9, v67, v38)
}
pub(super) fn if_26_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, condition: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24bv_5fbitwidth(s, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24bv_5fbitwidth(s, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_extract, &[v41, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Numeral(v46)) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_sign_5fextend, &[v47]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v45, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Numeral(v52)) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_sign_5fextend, &[v53]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v51, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(v58)) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_sign_5fextend, &[v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match eo__24eo_5ftypeof(s, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24eo_5fnil(s, v57, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v56, v63) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v50, v64, v44, v39, v12, v9, v38)
}
Some(false) => {
let v139 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match eo__24bv_5fbitwidth(s, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Numeral(v146)) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_core(EvalOp::Add, &[v145, v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_sign_5fextend, &[v148]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match eo__24bv_5fbitwidth(s, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.literal(Lit::Numeral(v152)) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.builtin_core(EvalOp::Add, &[v151, v153]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match eo__24bv_5fbitwidth(s, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.literal(Lit::Numeral(v157)) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.builtin_core(EvalOp::Add, &[v156, v158]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_extract, &[v154, v159]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v149, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v143, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v164, v165, v163, v142, v9, v12, v140, v139)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_27_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, condition: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fnil(s, v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v21, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v19, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Binary(BitVec::new(1, &v30))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24bv_5fbitwidth(s, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(v35)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::Eq, &[v34, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v763 = match if_26_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v37, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v763)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_28_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v764: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v764 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v764) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v765 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v766 = match s.construct(Constructor::eo_bvsmulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v767 = match s.apply(v766, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v768 = match s.apply(v767, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v769 = match s.apply(v765, v768) { Ok(v) => v, Err(e) => return Err(e) };
let v770 = match s.apply(v769, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v770)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_bvsmulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(v16)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Eq, &[v15, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v764 = match if_27_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v18, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v771 = match requires_28_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v764, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v771))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-smulo-elim"
pub fn eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_83_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsmulo_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v140: Term, v141: Term, v12: Term) -> CheckResult<Term> {
if v140 != v141 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v140) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v142 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(v143)) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Numeral(v145)) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match eo__24bv_5fbitwidth(s, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Numeral(v149)) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.builtin_core(EvalOp::Add, &[v148, v150]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.builtin_core(EvalOp::Add, &[v146, v151]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.literal(Lit::Numeral(v153)) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.builtin_core(EvalOp::Add, &[v152, v154]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.builtin_list(EvalOp::ListRepeat, &[v142, v144, v155]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.literal(Lit::Numeral(v157)) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match eo__24iota_5frec(s, v156, v158) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v159)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v12: Term, v130: Term, v9: Term, v32: Term, v128: Term, v20: Term) -> CheckResult<Term> {
let v131 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match eo__24bv_5fbitwidth(s, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.literal(Lit::Numeral(v133)) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_core(EvalOp::Add, &[v132, v134]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.builtin_core(EvalOp::Add, &[v130, v135]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Numeral(v137)) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_core(EvalOp::Add, &[v136, v138]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.builtin_core(EvalOp::IsNeg, &[v139]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match requires_0_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v140, v141, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match eo__24bv_5fbitwidth(s, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match eo__24bv_5fumulo_5felim_5frec(s, v12, v9, v32, v128, v160, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v20, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Binary(BitVec::new(1, &v165))) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v164, v166) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v167)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v9: Term, v102: Term, v98: Term, v12: Term, v97: Term, v85: Term, v80: Term, v79: Term, v32: Term, v20: Term) -> CheckResult<Term> {
let v103 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v103, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.literal(Lit::Binary(BitVec::new(0, &v105))) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v104, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v102, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v98, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Binary(BitVec::new(1, &v112))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v111, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Binary(BitVec::new(0, &v117))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v116, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v114, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match eo__24eo_5ftypeof(s, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match eo__24eo_5fnil(s, v110, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v109, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v97, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v85, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24eo_5ftypeof(s, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24eo_5fnil(s, v80, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v79, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Numeral(v129)) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v12, v130, v9, v32, v128, v20)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v62: Term, v75: Term, v50: Term, v38: Term, v33: Term, v12: Term, v9: Term, v32: Term, v20: Term) -> CheckResult<Term> {
let v76 = match s.apply(v62, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v50, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v38, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v33, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match eo__24bv_5fbitwidth(s, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match eo__24bv_5fbitwidth(s, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_extract, &[v82, v84]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Binary(BitVec::new(1, &v88))) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v87, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Binary(BitVec::new(0, &v93))) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v90, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v86, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Binary(BitVec::new(1, &v100))) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v99, v101) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v9, v102, v98, v12, v97, v85, v80, v79, v32, v20)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v45: Term, v47: Term, v43: Term, v39: Term, v9: Term, v12: Term, v38: Term, v33: Term, v32: Term, v20: Term) -> CheckResult<Term> {
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v43, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v39, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Binary(BitVec::new(1, &v53))) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v52, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Binary(BitVec::new(0, &v58))) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v57, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v55, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v51, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Binary(BitVec::new(1, &v65))) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Binary(BitVec::new(0, &v70))) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v69, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v67, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24eo_5ftypeof(s, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match eo__24eo_5fnil(s, v63, v74) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v62, v75, v50, v38, v33, v12, v9, v32, v20)
}
pub(super) fn if_5_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, condition: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24bv_5fbitwidth(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Add, &[v22, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24bv_5fbitwidth(s, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(v28)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Add, &[v27, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_extract, &[v25, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24bv_5fbitwidth(s, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24bv_5fbitwidth(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_extract, &[v35, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Binary(BitVec::new(1, &v41))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Binary(BitVec::new(0, &v46))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v45, v47, v43, v39, v9, v12, v38, v33, v32, v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_6_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v168: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v168 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v168) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v169 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_bvumulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v169, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v173, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v174)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_bvumulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24bv_5fbitwidth(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(v16)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Eq, &[v15, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match if_5_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v18, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match requires_6_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v168, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v175))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-umulo-elim"
pub fn eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_84_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fumulo_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s: &mut Store, v7: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v7 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24bv_5fmk_5fbitwise_5fslicing(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_0_eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s, v7, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-bitwise-slicing"
pub fn eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s, a0);
s.leave();
result
}
pub(super) fn case_85_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fbitwise_5fslicing, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dbitwise_2dslicing(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s: &mut Store, v7: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v7 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24bv_5fmk_5fbitblast_5fstep(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_0_eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s, v7, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv_bitblast_step"
pub fn eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s, a0);
s.leave();
result
}
pub(super) fn case_86_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fbitblast_5fstep, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_5fbitblast_5fstep(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(v16)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24bv_5fbitwidth(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Pow, &[v17, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24bv_5fbitwidth(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::IsNeg, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
Some(false) => {
let v22 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24bv_5fbitwidth(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v35 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(v35)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
Some(false) => {
let v37 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24bv_5fbitwidth(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_core(EvalOp::Pow, &[v38, v40]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v32 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24bv_5fbitwidth(s, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::IsNeg, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v34, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
Some(false) => {
let v43 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match eo__24bv_5fbitwidth(s, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v46)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, v49: Term, v50: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v49 != v50 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v49) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v51 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v53)
}
pub(super) fn if_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::ToRat, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v6, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(v2)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::IsEq, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match parse_rat("1/1") { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Rational(v24)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_4_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::IsBin, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match if_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
// EO program "$get_bv_poly_norm_rec"
pub fn eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(881), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(881), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_4_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24poly_5fneg(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24poly_5fadd(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_2_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24poly_5fneg(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24poly_5fadd(s, v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_3_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24poly_5fmul(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24poly_5fmod_5fcoeffs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$poly_mod_coeffs"
pub fn eo__24poly_5fmod_5fcoeffs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(943), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fmod_5fcoeffs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(943), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24poly_5fmod_5fcoeffs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24poly_5fmod_5fcoeffs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24poly_5fmod_5fcoeffs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24poly_5fmod_5fcoeffs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IntMod, &[v14, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(v16)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Eq, &[v15, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match if_0_eo__24poly_5fmod_5fcoeffs(s, v18, v2, a1, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn if_0_eo__24poly_5fmod_5fcoeffs(s: &mut Store, condition: Term, v2: Term, a1: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match eo__24poly_5fmod_5fcoeffs(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::IntMod, &[v23, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::ToRat, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v20, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24poly_5fmod_5fcoeffs(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24bv_5fbitwidth(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsZ, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_1_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24poly_5fmod_5fcoeffs(s, v7, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24bv_5fbitwidth(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::IsZ, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match if_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v31, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match eo__24poly_5fmod_5fcoeffs(s, v28, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::Eq, &[v27, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match requires_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v49, v50, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v54))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv_poly_norm"
pub fn eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, a0);
s.leave();
result
}
pub(super) fn case_87_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fpoly_5fnorm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_10_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_80_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_81_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_82_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_83_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_84_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_85_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_86_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_87_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v84: Term, v86: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v84 != v86 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v84) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v87 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v87, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v91, v94) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v95)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v78: Term, v80: Term, v56: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v78 != v80 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v78) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v81 = match s.builtin_core(EvalOp::ToInt, &[v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Numeral(v82)) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_core(EvalOp::IntMod, &[v81, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(v85)) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match requires_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v84, v86, v12, v9, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v96)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v72: Term, v74: Term, v35: Term, v56: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v72 != v74 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v72) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v75 = match s.builtin_core(EvalOp::ToInt, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(v76)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_core(EvalOp::IntMod, &[v75, v77]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(v79)) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match requires_1_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v78, v80, v56, v12, v9, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v97)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v72: Term, v74: Term, v35: Term, v56: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Option<Term>> {
let v98 = match requires_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v72, v74, v35, v56, v12, v9, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v98))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v41: Term, v43: Term, v42: Term, v12: Term, v9: Term, v25: Term, v19: Term, v16: Term, v39: Term, v35: Term) -> CheckResult<Option<Term>> {
if v41 != v43 { return Ok(None); }
let v44 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.unapply(v45) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v48 != v50 { return Ok(None); }
if v49 != v12 { return Ok(None); }
if v46 != v9 { return Ok(None); }
let v51 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
let v58 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != v19 { return Ok(None); }
if v67 != v16 { return Ok(None); }
if v60 != v39 { return Ok(None); }
let v72 = match s.builtin_core(EvalOp::ToInt, &[v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(v73)) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v72, v74, v35, v56, v12, v9, v19, v16)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v21 else { return Ok(None); }
;
let v22 = fields[0];
let v23 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.unapply(v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
let v36 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v41, v43, v42, v12, v9, v25, v19, v16, v39, v35)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv_poly_norm_eq"
pub fn eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, a0, a1);
s.leave();
result
}
pub(super) fn case_88_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5flength_5fpos(s: &mut Store, v22: Term, v24: Term, v21: Term, v20: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(v26)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v21, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v20, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5flength_5fpos(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24seq_5fempty(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v9, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v0, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5flength_5fpos(s, v22, v24, v21, v20)
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5flength_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5flength_5fpos(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_length_pos"
pub fn eo__24eo_5fprog_5fstring_5flength_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5flength_5fpos(s, a0);
s.leave();
result
}
pub(super) fn case_89_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5flength_5fpos, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstring_5flength_5fpos(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s: &mut Store, v13: Term, v14: Term, v11: Term) -> CheckResult<Term> {
if v13 != v14 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v13) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v15 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v15, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
pub(super) fn case_0_eo__24str_5fis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24str_5fis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24str_5fis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24str_5fis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_is_empty"
pub fn eo__24str_5fis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fis_5fempty(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match eo__24str_5fis_5fempty(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match requires_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s, v13, v14, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_length_non_empty"
pub fn eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s, a0);
s.leave();
result
}
pub(super) fn case_90_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5flength_5fnon_5fempty, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v13, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListRev, &[v12, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v16, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v20, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListRev, &[v19, v21]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
Some(false) => {
let v23 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v23, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v30, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_list(EvalOp::ListRev, &[v29, v31]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v33, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v34)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v37, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_list(EvalOp::ListRev, &[v36, v38]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v39)
}
Some(false) => {
let v40 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v40, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5fstrip_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
if v12 != v5 { return Ok(None); }
Ok(Some(Next::Again([v2, v9])))
}
pub(super) fn case_1_eo__24str_5fstrip_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn step_eo__24str_5fstrip_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fstrip_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fstrip_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5fstrip_5fprefix(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fstrip_5fprefix(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$str_strip_prefix"
pub fn eo__24str_5fstrip_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1073), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fstrip_5fprefix(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1073), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_0_eo__24eo_5fprog_5fconcat_5feq(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match if_1_eo__24eo_5fprog_5fconcat_5feq(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24str_5fstrip_5fprefix(s, v18, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24pair_5ffirst(s, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_list(EvalOp::ListRev, &[v11, v27]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
Some(false) => {
let v35 = match if_2_eo__24eo_5fprog_5fconcat_5feq(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_3_eo__24eo_5fprog_5fconcat_5feq(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24str_5fstrip_5fprefix(s, v35, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24pair_5ffirst(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v50 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v51, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_list(EvalOp::ListRev, &[v50, v52]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v53)
}
Some(false) => {
let v54 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v54, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v55)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v57 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v58, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_list(EvalOp::ListRev, &[v57, v59]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
Some(false) => {
let v61 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v61, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v67 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v68, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_list(EvalOp::ListRev, &[v67, v69]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
Some(false) => {
let v71 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v71, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v72)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v74 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v75, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.builtin_list(EvalOp::ListRev, &[v74, v76]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v77)
}
Some(false) => {
let v78 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v78, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v79)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v49 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match if_5_eo__24eo_5fprog_5fconcat_5feq(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match if_6_eo__24eo_5fprog_5fconcat_5feq(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24str_5fstrip_5fprefix(s, v56, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24pair_5fsecond(s, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_list(EvalOp::ListRev, &[v49, v65]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v66)
}
Some(false) => {
let v73 = match if_7_eo__24eo_5fprog_5fconcat_5feq(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match if_8_eo__24eo_5fprog_5fconcat_5feq(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match eo__24str_5fstrip_5fprefix(s, v73, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match eo__24pair_5fsecond(s, v81) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v82)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match if_4_eo__24eo_5fprog_5fconcat_5feq(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_list(EvalOp::ListSingletonElim, &[v10, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v9, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match if_9_eo__24eo_5fprog_5fconcat_5feq(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_list(EvalOp::ListSingletonElim, &[v48, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v47, v84) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v85))
}
pub(super) fn body_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fconcat_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_concat_eq"
pub fn eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fconcat_5feq(s, a0, a1);
s.leave();
result
}
pub(super) fn case_91_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econcat_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fconcat_5feq(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v28, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_list(EvalOp::ListRev, &[v27, v29]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
Some(false) => {
let v31 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v31, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v39, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_list(EvalOp::ListRev, &[v38, v40]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
Some(false) => {
let v42 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v42, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_2_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, v47: Term, v24: Term, v20: Term) -> CheckResult<Term> {
if v47 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v47) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v48 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v50)
}
pub(super) fn requires_3_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, v36: Term, v20: Term, a0: Term, v4: Term, v24: Term) -> CheckResult<Term> {
if v36 != v20 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v36) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_1_eo__24eo_5fprog_5fconcat_5funify(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(v45)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_list(EvalOp::ListNth, &[v37, v44, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match requires_2_eo__24eo_5fprog_5fconcat_5funify(s, v47, v24, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v51)
}
pub(super) fn case_0_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v9 else { return Ok(None); }
;
let v10 = fields[0];
let v11 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match if_0_eo__24eo_5fprog_5fconcat_5funify(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_list(EvalOp::ListNth, &[v26, v33, v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match requires_3_eo__24eo_5fprog_5fconcat_5funify(s, v36, v20, a0, v4, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v52))
}
pub(super) fn body_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fconcat_5funify(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_concat_unify"
pub fn eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fconcat_5funify(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_92_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econcat_5funify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = fields[1];
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5funify(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v30, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_list(EvalOp::ListRev, &[v29, v31]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v33, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v34)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v40 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v41, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListRev, &[v40, v42]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
Some(false) => {
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v44, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v76 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v77, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_list(EvalOp::ListRev, &[v76, v78]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v79)
}
Some(false) => {
let v80 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v80, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v81)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v110, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_list(EvalOp::ListRev, &[v109, v111]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v112)
}
Some(false) => {
let v113 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v113, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v114)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v139 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v140, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.builtin_list(EvalOp::ListRev, &[v139, v141]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v142)
}
Some(false) => {
let v143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v143, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v144)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v138: Term, v145: Term, v137: Term, v136: Term, v119: Term) -> CheckResult<Term> {
let v146 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Numeral(v146)) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_list(EvalOp::ListNth, &[v138, v145, v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match eo__24eo_5ftypeof(s, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match eo__24eo_5fnil(s, v137, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v136, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v119, v151) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v152)
}
pub(super) fn more_6_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v89: Term, v24: Term, v88: Term, v87: Term, v86: Term, v73: Term) -> CheckResult<Term> {
let v90 = match s.apply(v89, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.literal(Lit::Numeral(v91)) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v90, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v94, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Numeral(v98)) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v97, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v93, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v88, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match eo__24eo_5ftypeof(s, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match eo__24eo_5fnil(s, v87, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v86, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v73, v105) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v106)
}
pub(super) fn if_7_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v24: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v57 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(v61)) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v60, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(v68)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v63, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v58, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v57, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match if_2_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(v83)) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.builtin_list(EvalOp::ListNth, &[v75, v82, v84]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v74, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fconcat_5fcsplit(s, v89, v24, v88, v87, v86, v73)
}
Some(false) => {
let v107 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match if_3_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.literal(Lit::Numeral(v116)) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.builtin_list(EvalOp::ListNth, &[v108, v115, v117]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v107, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(v124)) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v123, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v127, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(v131)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v130, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v126, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v121, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v120, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match if_4_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fconcat_5fcsplit(s, v138, v145, v137, v136, v119)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_8_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v53: Term, v54: Term, v24: Term, a0: Term, v4: Term) -> CheckResult<Term> {
if v53 != v54 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v53) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match if_7_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v24, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v56, v153) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v154)
}
pub(super) fn requires_9_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v38: Term, v24: Term, a0: Term, v4: Term) -> CheckResult<Term> {
if v38 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v38) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match if_1_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_list(EvalOp::ListNth, &[v39, v46, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::Length, &[v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(v51)) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_core(EvalOp::IsEq, &[v50, v52]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match requires_8_eo__24eo_5fprog_5fconcat_5fcsplit(s, v53, v54, v24, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v155)
}
pub(super) fn case_0_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v9 else { return Ok(None); }
;
let v10 = fields[0];
let v11 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(v26)) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v27 { return Ok(None); }
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match if_0_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Numeral(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListNth, &[v28, v35, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match requires_9_eo__24eo_5fprog_5fconcat_5fcsplit(s, v38, v24, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v156))
}
pub(super) fn body_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_concat_csplit"
pub fn eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_93_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econcat_5fcsplit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = fields[1];
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5fcsplit(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v31 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v32, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListRev, &[v31, v33]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v34)
}
Some(false) => {
let v35 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v35, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v42 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v43, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_list(EvalOp::ListRev, &[v42, v44]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
Some(false) => {
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v46, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v47)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v56 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v57, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_list(EvalOp::ListRev, &[v56, v58]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v59)
}
Some(false) => {
let v60 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v60, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v61)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v70 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v71, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.builtin_list(EvalOp::ListRev, &[v70, v72]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v73)
}
Some(false) => {
let v74 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v74, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v75)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v81 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v82, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_list(EvalOp::ListRev, &[v81, v83]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v84)
}
Some(false) => {
let v85 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v85, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v86)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v96 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v97, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.builtin_list(EvalOp::ListRev, &[v96, v98]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v99)
}
Some(false) => {
let v100 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v100, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v101)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v110 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v111, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.builtin_list(EvalOp::ListRev, &[v110, v112]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v113)
}
Some(false) => {
let v114 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v114, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v115)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v139 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v140, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.builtin_list(EvalOp::ListRev, &[v139, v141]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v142)
}
Some(false) => {
let v143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v143, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v144)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v153 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v154, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.builtin_list(EvalOp::ListRev, &[v153, v155]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v156)
}
Some(false) => {
let v157 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v157, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v158)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v164 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v165, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.builtin_list(EvalOp::ListRev, &[v164, v166]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v167)
}
Some(false) => {
let v168 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v168, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v169)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v179 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v180, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.builtin_list(EvalOp::ListRev, &[v179, v181]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v182)
}
Some(false) => {
let v183 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v183, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v184)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_12_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v188: Term, v177: Term, v176: Term, v149: Term) -> CheckResult<Term> {
let v189 = match eo__24eo_5ftypeof(s, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match eo__24eo_5fnil(s, v177, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v176, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v149, v191) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v192)
}
pub(super) fn if_7_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v121 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v122, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_list(EvalOp::ListRev, &[v121, v123]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v124)
}
Some(false) => {
let v125 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v125, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v126)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_0_eo__24str_5funify_5fsplit(s: &mut Store, a1: Term, a0: Term, v23: Term) -> CheckResult<Option<Term>> {
let v24 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(v26)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v23, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn case_0_eo__24str_5funify_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(v12)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v9, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5funify_5fsplit(s, a1, a0, v23)
}
pub(super) fn more_1_eo__24str_5funify_5fsplit(s: &mut Store, v9: Term, v22: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v23 = match s.apply(v9, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v23, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn case_1_eo__24str_5funify_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5funify_5fsplit(s, v9, v22, a1, a0)
}
pub(super) fn body_eo__24str_5funify_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5funify_5fsplit(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5funify_5fsplit(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_unify_split"
pub fn eo__24str_5funify_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5funify_5fsplit(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn more_13_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v109: Term, v116: Term, v118: Term, a0: Term, v4: Term, v108: Term, v107: Term, v106: Term, v93: Term) -> CheckResult<Term> {
let v119 = match s.builtin_list(EvalOp::ListNth, &[v109, v116, v118]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match if_7_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Numeral(v128)) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_list(EvalOp::ListNth, &[v120, v127, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match eo__24str_5funify_5fsplit(s, v119, v130, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v108, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match eo__24eo_5ftypeof(s, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match eo__24eo_5fnil(s, v107, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v106, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v93, v135) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v136)
}
pub(super) fn if_14_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v67 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match if_3_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Numeral(v77)) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_list(EvalOp::ListNth, &[v69, v76, v78]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match if_4_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Numeral(v88)) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_list(EvalOp::ListNth, &[v80, v87, v89]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match eo__24str_5funify_5fsplit(s, v79, v90, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v68, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v67, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match if_5_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(v103)) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.builtin_list(EvalOp::ListNth, &[v95, v102, v104]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v94, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match if_6_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(v117)) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fconcat_5fsplit(s, v109, v116, v118, a0, v4, v108, v107, v106, v93)
}
Some(false) => {
let v137 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match if_8_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Numeral(v146)) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_list(EvalOp::ListNth, &[v138, v145, v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v137, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match if_9_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.literal(Lit::Numeral(v160)) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListNth, &[v152, v159, v161]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match if_10_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.literal(Lit::Numeral(v171)) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.builtin_list(EvalOp::ListNth, &[v163, v170, v172]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match eo__24str_5funify_5fsplit(s, v162, v173, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v151, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v150, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match if_11_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.literal(Lit::Numeral(v186)) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.builtin_list(EvalOp::ListNth, &[v178, v185, v187]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fconcat_5fsplit(s, v188, v177, v176, v149)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v199 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v200, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.builtin_list(EvalOp::ListRev, &[v199, v201]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v202)
}
Some(false) => {
let v203 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v203, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v204)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v213 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v214, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.builtin_list(EvalOp::ListRev, &[v213, v215]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v216)
}
Some(false) => {
let v217 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v217, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v218)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v224 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v225, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_list(EvalOp::ListRev, &[v224, v226]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v227)
}
Some(false) => {
let v228 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v228, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v229)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v239 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v240, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.builtin_list(EvalOp::ListRev, &[v239, v241]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v242)
}
Some(false) => {
let v243 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v243, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v244)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v253 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v254, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.builtin_list(EvalOp::ListRev, &[v253, v255]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v256)
}
Some(false) => {
let v257 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v257, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v258)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v282 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v283, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.builtin_list(EvalOp::ListRev, &[v282, v284]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v285)
}
Some(false) => {
let v286 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v286, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v287)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_22_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v296 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v297, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.builtin_list(EvalOp::ListRev, &[v296, v298]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v299)
}
Some(false) => {
let v300 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v300, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v301)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_23_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v307 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v308, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.builtin_list(EvalOp::ListRev, &[v307, v309]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v310)
}
Some(false) => {
let v311 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v311, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v312)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_24_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v322 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v323, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.builtin_list(EvalOp::ListRev, &[v322, v324]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v325)
}
Some(false) => {
let v326 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v326, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v327)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_25_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v331: Term, v320: Term, v319: Term, v292: Term) -> CheckResult<Term> {
let v332 = match eo__24eo_5ftypeof(s, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match eo__24eo_5fnil(s, v320, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v319, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v292, v334) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v335)
}
pub(super) fn if_20_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v264 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v265, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.builtin_list(EvalOp::ListRev, &[v264, v266]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v267)
}
Some(false) => {
let v268 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v268, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v269)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_26_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v252: Term, v259: Term, v261: Term, a0: Term, v4: Term, v251: Term, v250: Term, v249: Term, v236: Term) -> CheckResult<Term> {
let v262 = match s.builtin_list(EvalOp::ListNth, &[v252, v259, v261]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match if_20_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.literal(Lit::Numeral(v271)) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.builtin_list(EvalOp::ListNth, &[v263, v270, v272]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match eo__24str_5funify_5fsplit(s, v262, v273, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v251, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match eo__24eo_5ftypeof(s, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match eo__24eo_5fnil(s, v250, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v249, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v236, v278) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v279)
}
pub(super) fn if_27_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v210 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match if_16_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.literal(Lit::Numeral(v220)) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.builtin_list(EvalOp::ListNth, &[v212, v219, v221]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match if_17_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.literal(Lit::Numeral(v231)) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.builtin_list(EvalOp::ListNth, &[v223, v230, v232]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match eo__24str_5funify_5fsplit(s, v222, v233, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v211, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v210, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match if_18_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.literal(Lit::Numeral(v246)) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.builtin_list(EvalOp::ListNth, &[v238, v245, v247]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v237, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match if_19_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.literal(Lit::Numeral(v260)) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24eo_5fprog_5fconcat_5fsplit(s, v252, v259, v261, a0, v4, v251, v250, v249, v236)
}
Some(false) => {
let v280 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match if_21_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.literal(Lit::Numeral(v289)) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.builtin_list(EvalOp::ListNth, &[v281, v288, v290]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.apply(v280, v291) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match if_22_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.literal(Lit::Numeral(v303)) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.builtin_list(EvalOp::ListNth, &[v295, v302, v304]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match if_23_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.literal(Lit::Numeral(v314)) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.builtin_list(EvalOp::ListNth, &[v306, v313, v315]) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match eo__24str_5funify_5fsplit(s, v305, v316, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v294, v317) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v293, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match if_24_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.literal(Lit::Numeral(v329)) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.builtin_list(EvalOp::ListNth, &[v321, v328, v330]) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24eo_5fprog_5fconcat_5fsplit(s, v331, v320, v319, v292)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_28_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v348 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v349, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.builtin_list(EvalOp::ListRev, &[v348, v350]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v351)
}
Some(false) => {
let v352 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v352, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v353)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_29_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v359 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v360, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.builtin_list(EvalOp::ListRev, &[v359, v361]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v362)
}
Some(false) => {
let v363 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v363, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v364)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_30_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v374 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v375, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.builtin_list(EvalOp::ListRev, &[v374, v376]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v377)
}
Some(false) => {
let v378 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v378, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v379)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_31_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v385 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v386, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.builtin_list(EvalOp::ListRev, &[v385, v387]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v388)
}
Some(false) => {
let v389 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v389, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v390)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_32_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v407 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v408, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.builtin_list(EvalOp::ListRev, &[v407, v409]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v410)
}
Some(false) => {
let v411 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v411, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v412)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_33_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v418 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v419, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.builtin_list(EvalOp::ListRev, &[v418, v420]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v421)
}
Some(false) => {
let v422 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v422, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v423)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_36_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v431: Term, v402: Term, v401: Term, v342: Term) -> CheckResult<Term> {
let v432 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.literal(Lit::Numeral(v432)) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.apply(v431, v433) { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match s.apply(v402, v434) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match s.apply(v435, v436) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.apply(v401, v437) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match s.apply(v342, v438) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v439)
}
pub(super) fn more_35_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v384: Term, v391: Term, v393: Term, v383: Term, a0: Term, v372: Term, v371: Term, v344: Term, v343: Term, v7: Term, v4: Term, v342: Term) -> CheckResult<Term> {
let v394 = match s.builtin_list(EvalOp::ListNth, &[v384, v391, v393]) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match eo__24str_5funify_5fsplit(s, v383, v394, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.apply(v372, v395) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match eo__24eo_5ftypeof(s, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match eo__24seq_5fempty(s, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.apply(v371, v398) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.apply(v344, v399) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.apply(v343, v400) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match if_32_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.literal(Lit::Numeral(v414)) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.builtin_list(EvalOp::ListNth, &[v406, v413, v415]) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match if_33_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.literal(Lit::Numeral(v425)) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.builtin_list(EvalOp::ListNth, &[v417, v424, v426]) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match eo__24str_5funify_5fsplit(s, v416, v427, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.apply(v405, v428) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match s.apply(v404, v429) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.apply(v403, v430) { Ok(v) => v, Err(e) => return Err(e) };
more_36_eo__24eo_5fprog_5fconcat_5fsplit(s, v431, v402, v401, v342)
}
pub(super) fn more_34_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v52: Term, v341: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let v342 = match s.apply(v52, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match if_28_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.literal(Lit::Numeral(v355)) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.builtin_list(EvalOp::ListNth, &[v347, v354, v356]) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match if_29_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.literal(Lit::Numeral(v366)) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.builtin_list(EvalOp::ListNth, &[v358, v365, v367]) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match eo__24str_5funify_5fsplit(s, v357, v368, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.apply(v346, v369) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.apply(v345, v370) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match if_30_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.literal(Lit::Numeral(v381)) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.builtin_list(EvalOp::ListNth, &[v373, v380, v382]) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match if_31_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.literal(Lit::Numeral(v392)) { Ok(v) => v, Err(e) => return Err(e) };
more_35_eo__24eo_5fprog_5fconcat_5fsplit(s, v384, v391, v393, v383, a0, v372, v371, v344, v343, v7, v4, v342)
}
pub(super) fn requires_37_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v51: Term, v28: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
if v51 != v28 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v51) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v52 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match if_2_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Numeral(v63)) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.builtin_list(EvalOp::ListNth, &[v55, v62, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v54, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match if_14_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v66, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v53, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match if_15_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.literal(Lit::Numeral(v206)) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.builtin_list(EvalOp::ListNth, &[v198, v205, v207]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v197, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match if_27_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.apply(v209, v336) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v196, v337) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v338, v339) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v195, v340) { Ok(v) => v, Err(e) => return Err(e) };
more_34_eo__24eo_5fprog_5fconcat_5fsplit(s, v52, v341, a0, v7, v4)
}
pub(super) fn requires_38_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v40: Term, v24: Term, a0: Term, v4: Term, v28: Term, v7: Term) -> CheckResult<Term> {
if v40 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v40) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match if_1_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Numeral(v49)) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.builtin_list(EvalOp::ListNth, &[v41, v48, v50]) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match requires_37_eo__24eo_5fprog_5fconcat_5fsplit(s, v51, v28, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v440)
}
pub(super) fn case_0_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v9 else { return Ok(None); }
;
let v10 = fields[0];
let v11 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match if_0_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(v38)) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_list(EvalOp::ListNth, &[v30, v37, v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match requires_38_eo__24eo_5fprog_5fconcat_5fsplit(s, v40, v24, a0, v4, v28, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v441))
}
pub(super) fn body_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_concat_split"
pub fn eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_94_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econcat_5fsplit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = fields[1];
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5fsplit(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v28, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_list(EvalOp::ListRev, &[v27, v29]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
Some(false) => {
let v31 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v31, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v39, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_list(EvalOp::ListRev, &[v38, v40]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
Some(false) => {
let v42 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v42, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v51 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v52, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.builtin_list(EvalOp::ListRev, &[v51, v53]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v54)
}
Some(false) => {
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v55, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v56)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v65 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v66, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_list(EvalOp::ListRev, &[v65, v67]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v68)
}
Some(false) => {
let v69 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v69, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v76 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v77, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_list(EvalOp::ListRev, &[v76, v78]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v79)
}
Some(false) => {
let v80 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v80, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v81)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v91 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v92, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.builtin_list(EvalOp::ListRev, &[v91, v93]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v94)
}
Some(false) => {
let v95 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v95, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v96)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v105 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v106, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_list(EvalOp::ListRev, &[v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v108)
}
Some(false) => {
let v109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v109, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v110)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v134 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v135, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_list(EvalOp::ListRev, &[v134, v136]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v137)
}
Some(false) => {
let v138 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v138, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v139)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v148 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v149, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.builtin_list(EvalOp::ListRev, &[v148, v150]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v151)
}
Some(false) => {
let v152 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v152, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v153)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v159 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v160, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListRev, &[v159, v161]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v162)
}
Some(false) => {
let v163 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v163, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v164)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v174 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v175, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListRev, &[v174, v176]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v177)
}
Some(false) => {
let v178 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v178, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v179)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_12_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v183: Term, v172: Term, v171: Term, v144: Term) -> CheckResult<Term> {
let v184 = match eo__24eo_5ftypeof(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match eo__24eo_5fnil(s, v172, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v171, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v144, v186) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v187)
}
pub(super) fn if_7_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v116 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v117, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.builtin_list(EvalOp::ListRev, &[v116, v118]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v119)
}
Some(false) => {
let v120 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v120, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v121)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_13_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v104: Term, v111: Term, v113: Term, a0: Term, v4: Term, v103: Term, v102: Term, v101: Term, v88: Term) -> CheckResult<Term> {
let v114 = match s.builtin_list(EvalOp::ListNth, &[v104, v111, v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match if_7_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.literal(Lit::Numeral(v123)) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.builtin_list(EvalOp::ListNth, &[v115, v122, v124]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24str_5funify_5fsplit(s, v114, v125, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v103, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match eo__24eo_5ftypeof(s, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24eo_5fnil(s, v102, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v101, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v88, v130) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v131)
}
pub(super) fn if_14_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v62 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match if_3_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Numeral(v72)) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_list(EvalOp::ListNth, &[v64, v71, v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match if_4_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(v83)) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.builtin_list(EvalOp::ListNth, &[v75, v82, v84]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24str_5funify_5fsplit(s, v74, v85, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v63, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v62, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match if_5_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Numeral(v98)) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.builtin_list(EvalOp::ListNth, &[v90, v97, v99]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v89, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match if_6_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(v112)) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fconcat_5flprop(s, v104, v111, v113, a0, v4, v103, v102, v101, v88)
}
Some(false) => {
let v132 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match if_8_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.literal(Lit::Numeral(v141)) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.builtin_list(EvalOp::ListNth, &[v133, v140, v142]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v132, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match if_9_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Numeral(v155)) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.builtin_list(EvalOp::ListNth, &[v147, v154, v156]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match if_10_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Numeral(v166)) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.builtin_list(EvalOp::ListNth, &[v158, v165, v167]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match eo__24str_5funify_5fsplit(s, v157, v168, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v146, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v145, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match if_11_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.literal(Lit::Numeral(v181)) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.builtin_list(EvalOp::ListNth, &[v173, v180, v182]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fconcat_5flprop(s, v183, v172, v171, v144)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v196 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v197, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.builtin_list(EvalOp::ListRev, &[v196, v198]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v199)
}
Some(false) => {
let v200 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v200, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v201)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v207 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v208, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_list(EvalOp::ListRev, &[v207, v209]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v210)
}
Some(false) => {
let v211 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v211, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v212)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v222 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v223, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.builtin_list(EvalOp::ListRev, &[v222, v224]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v225)
}
Some(false) => {
let v226 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v226, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v227)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v233 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v234, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.builtin_list(EvalOp::ListRev, &[v233, v235]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v236)
}
Some(false) => {
let v237 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v237, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v238)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v255 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v256, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.builtin_list(EvalOp::ListRev, &[v255, v257]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v258)
}
Some(false) => {
let v259 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v259, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v260)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_20_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v266 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v267, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.builtin_list(EvalOp::ListRev, &[v266, v268]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v269)
}
Some(false) => {
let v270 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v270, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v271)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_22_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v254: Term, v261: Term, v263: Term, a0: Term, v4: Term, v253: Term, v252: Term, v251: Term, v250: Term, v249: Term, v190: Term) -> CheckResult<Term> {
let v264 = match s.builtin_list(EvalOp::ListNth, &[v254, v261, v263]) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match if_20_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.literal(Lit::Numeral(v273)) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.builtin_list(EvalOp::ListNth, &[v265, v272, v274]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match eo__24str_5funify_5fsplit(s, v264, v275, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v253, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v252, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v251, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.literal(Lit::Numeral(v280)) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v279, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v250, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.apply(v283, v284) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v249, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v190, v286) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v287)
}
pub(super) fn more_21_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v193: Term, v218: Term, a0: Term, v7: Term, v4: Term, v192: Term, v191: Term, v190: Term) -> CheckResult<Term> {
let v219 = match s.apply(v193, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match if_17_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(v229)) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.builtin_list(EvalOp::ListNth, &[v221, v228, v230]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match if_18_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.literal(Lit::Numeral(v240)) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.builtin_list(EvalOp::ListNth, &[v232, v239, v241]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match eo__24str_5funify_5fsplit(s, v231, v242, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v220, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match eo__24eo_5ftypeof(s, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match eo__24seq_5fempty(s, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v219, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v192, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v191, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match if_19_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.literal(Lit::Numeral(v262)) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24eo_5fprog_5fconcat_5flprop(s, v254, v261, v263, a0, v4, v253, v252, v251, v250, v249, v190)
}
pub(super) fn requires_23_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v47: Term, v24: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
if v47 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v47) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v48 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match if_2_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(v58)) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_list(EvalOp::ListNth, &[v50, v57, v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v49, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match if_14_eo__24eo_5fprog_5fconcat_5flprop(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v61, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v48, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match if_15_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.literal(Lit::Numeral(v203)) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.builtin_list(EvalOp::ListNth, &[v195, v202, v204]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match if_16_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.literal(Lit::Numeral(v214)) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.builtin_list(EvalOp::ListNth, &[v206, v213, v215]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match eo__24str_5funify_5fsplit(s, v205, v216, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v194, v217) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24eo_5fprog_5fconcat_5flprop(s, v193, v218, a0, v7, v4, v192, v191, v190)
}
pub(super) fn requires_24_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v36: Term, v20: Term, a0: Term, v4: Term, v24: Term, v7: Term) -> CheckResult<Term> {
if v36 != v20 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v36) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_1_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(v45)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_list(EvalOp::ListNth, &[v37, v44, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match requires_23_eo__24eo_5fprog_5fconcat_5flprop(s, v47, v24, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v288)
}
pub(super) fn case_0_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v9 else { return Ok(None); }
;
let v10 = fields[0];
let v11 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match if_0_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_list(EvalOp::ListNth, &[v26, v33, v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match requires_24_eo__24eo_5fprog_5fconcat_5flprop(s, v36, v20, a0, v4, v24, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v289))
}
pub(super) fn body_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fconcat_5flprop(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_concat_lprop"
pub fn eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fconcat_5flprop(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_95_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econcat_5flprop, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = fields[1];
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5flprop(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn cases_11_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_88_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_89_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_90_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_91_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_92_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_93_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_94_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_95_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v30, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_list(EvalOp::ListRev, &[v29, v31]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v33, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v34)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v56, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.builtin_list(EvalOp::ListRev, &[v55, v57]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v58)
}
Some(false) => {
let v59 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v59, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v69 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v70, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.builtin_list(EvalOp::ListRev, &[v69, v71]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v72)
}
Some(false) => {
let v73 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v73, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v74)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_91_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1112 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1113 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1114 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1113, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1115 = match s.builtin_list(EvalOp::ListRev, &[v1112, v1114]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1115)
}
Some(false) => {
let v1116 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1117 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1116, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1117)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_92_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1132 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1133 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1132, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1134 = match s.builtin_list(EvalOp::ListRev, &[v1131, v1133]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1134)
}
Some(false) => {
let v1135 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1136 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1135, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1136)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_93_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1144 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1146 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1145, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1147 = match s.builtin_list(EvalOp::ListRev, &[v1144, v1146]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1147)
}
Some(false) => {
let v1148 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1149 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1148, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1149)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_94_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1160 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1161 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1162 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1161, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1163 = match s.builtin_list(EvalOp::ListRev, &[v1160, v1162]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1163)
}
Some(false) => {
let v1164 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1165 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1164, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1165)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_95_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1173 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1174 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1175 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1174, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1176 = match s.builtin_list(EvalOp::ListRev, &[v1173, v1175]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1176)
}
Some(false) => {
let v1177 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1178 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1177, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1178)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_96_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1130 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1137 = match if_92_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1138 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1139 = match s.literal(Lit::Numeral(v1138)) { Ok(v) => v, Err(e) => return Err(e) };
let v1140 = match s.builtin_list(EvalOp::ListNth, &[v1130, v1137, v1139]) { Ok(v) => v, Err(e) => return Err(e) };
let v1141 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1142 = match s.literal(Lit::Numeral(v1141)) { Ok(v) => v, Err(e) => return Err(e) };
let v1143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1150 = match if_93_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1151 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1152 = match s.literal(Lit::Numeral(v1151)) { Ok(v) => v, Err(e) => return Err(e) };
let v1153 = match s.builtin_list(EvalOp::ListNth, &[v1143, v1150, v1152]) { Ok(v) => v, Err(e) => return Err(e) };
let v1154 = match s.builtin_core(EvalOp::Length, &[v1153]) { Ok(v) => v, Err(e) => return Err(e) };
let v1155 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1156 = match s.literal(Lit::Numeral(v1155)) { Ok(v) => v, Err(e) => return Err(e) };
let v1157 = match s.builtin_core(EvalOp::Add, &[v1154, v1156]) { Ok(v) => v, Err(e) => return Err(e) };
let v1158 = match s.builtin_core(EvalOp::Extract, &[v1140, v1142, v1157]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1158)
}
Some(false) => {
let v1159 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1166 = match if_94_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1167 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1168 = match s.literal(Lit::Numeral(v1167)) { Ok(v) => v, Err(e) => return Err(e) };
let v1169 = match s.builtin_list(EvalOp::ListNth, &[v1159, v1166, v1168]) { Ok(v) => v, Err(e) => return Err(e) };
let v1170 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1171 = match s.literal(Lit::Numeral(v1170)) { Ok(v) => v, Err(e) => return Err(e) };
let v1172 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1179 = match if_95_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1180 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1181 = match s.literal(Lit::Numeral(v1180)) { Ok(v) => v, Err(e) => return Err(e) };
let v1182 = match s.builtin_list(EvalOp::ListNth, &[v1172, v1179, v1181]) { Ok(v) => v, Err(e) => return Err(e) };
let v1183 = match s.builtin_core(EvalOp::Length, &[v1182]) { Ok(v) => v, Err(e) => return Err(e) };
let v1184 = match s.builtin_core(EvalOp::Extract, &[v1169, v1171, v1183]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1184)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_97_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1191 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1192 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1193 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1192, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1194 = match s.builtin_list(EvalOp::ListRev, &[v1191, v1193]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1194)
}
Some(false) => {
let v1195 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1196 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1195, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1196)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_98_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1204 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1205 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1206 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1205, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1207 = match s.builtin_list(EvalOp::ListRev, &[v1204, v1206]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1207)
}
Some(false) => {
let v1208 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1209 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1208, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1209)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_99_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1220 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1221 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1222 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1221, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1223 = match s.builtin_list(EvalOp::ListRev, &[v1220, v1222]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1223)
}
Some(false) => {
let v1224 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1225 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1224, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1225)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_100_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1233 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1234 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1235 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1234, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1236 = match s.builtin_list(EvalOp::ListRev, &[v1233, v1235]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1236)
}
Some(false) => {
let v1237 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1238 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1237, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1238)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_101_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1190 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1197 = match if_97_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1198 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1199 = match s.literal(Lit::Numeral(v1198)) { Ok(v) => v, Err(e) => return Err(e) };
let v1200 = match s.builtin_list(EvalOp::ListNth, &[v1190, v1197, v1199]) { Ok(v) => v, Err(e) => return Err(e) };
let v1201 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1202 = match s.literal(Lit::Numeral(v1201)) { Ok(v) => v, Err(e) => return Err(e) };
let v1203 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1210 = match if_98_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1211 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1212 = match s.literal(Lit::Numeral(v1211)) { Ok(v) => v, Err(e) => return Err(e) };
let v1213 = match s.builtin_list(EvalOp::ListNth, &[v1203, v1210, v1212]) { Ok(v) => v, Err(e) => return Err(e) };
let v1214 = match s.builtin_core(EvalOp::Length, &[v1213]) { Ok(v) => v, Err(e) => return Err(e) };
let v1215 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1216 = match s.literal(Lit::Numeral(v1215)) { Ok(v) => v, Err(e) => return Err(e) };
let v1217 = match s.builtin_core(EvalOp::Add, &[v1214, v1216]) { Ok(v) => v, Err(e) => return Err(e) };
let v1218 = match s.builtin_core(EvalOp::Extract, &[v1200, v1202, v1217]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1218)
}
Some(false) => {
let v1219 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1226 = match if_99_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1227 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1228 = match s.literal(Lit::Numeral(v1227)) { Ok(v) => v, Err(e) => return Err(e) };
let v1229 = match s.builtin_list(EvalOp::ListNth, &[v1219, v1226, v1228]) { Ok(v) => v, Err(e) => return Err(e) };
let v1230 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1231 = match s.literal(Lit::Numeral(v1230)) { Ok(v) => v, Err(e) => return Err(e) };
let v1232 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1239 = match if_100_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1240 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1241 = match s.literal(Lit::Numeral(v1240)) { Ok(v) => v, Err(e) => return Err(e) };
let v1242 = match s.builtin_list(EvalOp::ListNth, &[v1232, v1239, v1241]) { Ok(v) => v, Err(e) => return Err(e) };
let v1243 = match s.builtin_core(EvalOp::Length, &[v1242]) { Ok(v) => v, Err(e) => return Err(e) };
let v1244 = match s.builtin_core(EvalOp::Extract, &[v1229, v1231, v1243]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1244)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_0_eo__24str_5fflatten(s: &mut Store, v10: Term, v11: Term, v5: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListRepeat, &[v12, v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(v17)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24iota_5frec(s, v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
pub(super) fn case_0_eo__24str_5fflatten_5fword_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$str_flatten_word_rec"
pub fn eo__24str_5fflatten_5fword_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1045), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fflatten_5fword_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1045), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fflatten_5fword_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fflatten_5fword_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fflatten_5fword_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24str_5fflatten_5fword_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Extract, &[a1, v5, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24str_5fflatten_5fword_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn requires_2_eo__24str_5fflatten(s: &mut Store, a0: Term, v1: Term) -> CheckResult<Term> {
if a0 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_2_eo__24str_5fflatten(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24seq_5fempty(s, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match requires_2_eo__24str_5fflatten(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
// EO program "$str_flatten"
pub fn eo__24str_5fflatten(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1044), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fflatten(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1044), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fflatten(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fflatten(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fflatten(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fflatten(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fflatten(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24str_5fflatten(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5fflatten(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListConcat, &[v14, v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_1_eo__24str_5fflatten(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsStr, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_1_eo__24str_5fflatten(s, v7, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn if_1_eo__24str_5fflatten(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match requires_0_eo__24str_5fflatten(s, v10, v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24str_5fflatten_5fword_5frec(s, v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fflatten(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v8, v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24str_5fflatten(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_102_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1128 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1129 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1185 = match if_96_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1186 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1129, v1185]) { Ok(v) => v, Err(e) => return Err(e) };
let v1187 = match eo__24str_5fflatten(s, v1186) { Ok(v) => v, Err(e) => return Err(e) };
let v1188 = match s.builtin_list(EvalOp::ListRev, &[v1128, v1187]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1188)
}
Some(false) => {
let v1189 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1245 = match if_101_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1246 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1189, v1245]) { Ok(v) => v, Err(e) => return Err(e) };
let v1247 = match eo__24str_5fflatten(s, v1246) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1247)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_103_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1252 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1253 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1254 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1253, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1255 = match s.builtin_list(EvalOp::ListRev, &[v1252, v1254]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1255)
}
Some(false) => {
let v1256 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1257 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1256, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1257)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_104_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1267 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1268 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1269 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1268, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1270 = match s.builtin_list(EvalOp::ListRev, &[v1267, v1269]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1270)
}
Some(false) => {
let v1271 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1272 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1271, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1272)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_105_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1249 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1250 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1251 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1258 = match if_103_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1259 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1260 = match s.literal(Lit::Numeral(v1259)) { Ok(v) => v, Err(e) => return Err(e) };
let v1261 = match s.builtin_list(EvalOp::ListNth, &[v1251, v1258, v1260]) { Ok(v) => v, Err(e) => return Err(e) };
let v1262 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1250, v1261]) { Ok(v) => v, Err(e) => return Err(e) };
let v1263 = match eo__24str_5fflatten(s, v1262) { Ok(v) => v, Err(e) => return Err(e) };
let v1264 = match s.builtin_list(EvalOp::ListRev, &[v1249, v1263]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1264)
}
Some(false) => {
let v1265 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1266 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1273 = match if_104_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1274 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1275 = match s.literal(Lit::Numeral(v1274)) { Ok(v) => v, Err(e) => return Err(e) };
let v1276 = match s.builtin_list(EvalOp::ListNth, &[v1266, v1273, v1275]) { Ok(v) => v, Err(e) => return Err(e) };
let v1277 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1265, v1276]) { Ok(v) => v, Err(e) => return Err(e) };
let v1278 = match eo__24str_5fflatten(s, v1277) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1278)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_106_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1291 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1292 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1293 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1292, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1294 = match s.builtin_list(EvalOp::ListRev, &[v1291, v1293]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1294)
}
Some(false) => {
let v1295 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1296 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1295, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1296)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_107_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1310 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1311 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1312 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1311, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1313 = match s.builtin_list(EvalOp::ListRev, &[v1310, v1312]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1313)
}
Some(false) => {
let v1314 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1315 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1314, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1315)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_108_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1323 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1324 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1325 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1324, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1326 = match s.builtin_list(EvalOp::ListRev, &[v1323, v1325]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1326)
}
Some(false) => {
let v1327 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1328 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1327, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1328)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_109_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1339 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1340 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1341 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1340, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1342 = match s.builtin_list(EvalOp::ListRev, &[v1339, v1341]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1342)
}
Some(false) => {
let v1343 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1344 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1343, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1344)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_110_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1352 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1353 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1354 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1353, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1355 = match s.builtin_list(EvalOp::ListRev, &[v1352, v1354]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1355)
}
Some(false) => {
let v1356 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1357 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1356, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1357)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_111_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1309 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1316 = match if_107_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1317 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1318 = match s.literal(Lit::Numeral(v1317)) { Ok(v) => v, Err(e) => return Err(e) };
let v1319 = match s.builtin_list(EvalOp::ListNth, &[v1309, v1316, v1318]) { Ok(v) => v, Err(e) => return Err(e) };
let v1320 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1321 = match s.literal(Lit::Numeral(v1320)) { Ok(v) => v, Err(e) => return Err(e) };
let v1322 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1329 = match if_108_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1330 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1331 = match s.literal(Lit::Numeral(v1330)) { Ok(v) => v, Err(e) => return Err(e) };
let v1332 = match s.builtin_list(EvalOp::ListNth, &[v1322, v1329, v1331]) { Ok(v) => v, Err(e) => return Err(e) };
let v1333 = match s.builtin_core(EvalOp::Length, &[v1332]) { Ok(v) => v, Err(e) => return Err(e) };
let v1334 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1335 = match s.literal(Lit::Numeral(v1334)) { Ok(v) => v, Err(e) => return Err(e) };
let v1336 = match s.builtin_core(EvalOp::Add, &[v1333, v1335]) { Ok(v) => v, Err(e) => return Err(e) };
let v1337 = match s.builtin_core(EvalOp::Extract, &[v1319, v1321, v1336]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1337)
}
Some(false) => {
let v1338 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1345 = match if_109_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1346 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1347 = match s.literal(Lit::Numeral(v1346)) { Ok(v) => v, Err(e) => return Err(e) };
let v1348 = match s.builtin_list(EvalOp::ListNth, &[v1338, v1345, v1347]) { Ok(v) => v, Err(e) => return Err(e) };
let v1349 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1350 = match s.literal(Lit::Numeral(v1349)) { Ok(v) => v, Err(e) => return Err(e) };
let v1351 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1358 = match if_110_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1359 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1360 = match s.literal(Lit::Numeral(v1359)) { Ok(v) => v, Err(e) => return Err(e) };
let v1361 = match s.builtin_list(EvalOp::ListNth, &[v1351, v1358, v1360]) { Ok(v) => v, Err(e) => return Err(e) };
let v1362 = match s.builtin_core(EvalOp::Length, &[v1361]) { Ok(v) => v, Err(e) => return Err(e) };
let v1363 = match s.builtin_core(EvalOp::Extract, &[v1348, v1350, v1362]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1363)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_112_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1370 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1371 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1372 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1371, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1373 = match s.builtin_list(EvalOp::ListRev, &[v1370, v1372]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1373)
}
Some(false) => {
let v1374 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1375 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1374, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1375)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_113_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1383 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1384 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1385 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1384, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1386 = match s.builtin_list(EvalOp::ListRev, &[v1383, v1385]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1386)
}
Some(false) => {
let v1387 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1388 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1387, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1388)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_114_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1399 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1400 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1401 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1400, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1402 = match s.builtin_list(EvalOp::ListRev, &[v1399, v1401]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1402)
}
Some(false) => {
let v1403 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1404 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1403, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1404)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_115_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1412 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1413 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1414 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1413, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1415 = match s.builtin_list(EvalOp::ListRev, &[v1412, v1414]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1415)
}
Some(false) => {
let v1416 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1417 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1416, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1417)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_116_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1369 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1376 = match if_112_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1377 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1378 = match s.literal(Lit::Numeral(v1377)) { Ok(v) => v, Err(e) => return Err(e) };
let v1379 = match s.builtin_list(EvalOp::ListNth, &[v1369, v1376, v1378]) { Ok(v) => v, Err(e) => return Err(e) };
let v1380 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1381 = match s.literal(Lit::Numeral(v1380)) { Ok(v) => v, Err(e) => return Err(e) };
let v1382 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1389 = match if_113_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1390 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1391 = match s.literal(Lit::Numeral(v1390)) { Ok(v) => v, Err(e) => return Err(e) };
let v1392 = match s.builtin_list(EvalOp::ListNth, &[v1382, v1389, v1391]) { Ok(v) => v, Err(e) => return Err(e) };
let v1393 = match s.builtin_core(EvalOp::Length, &[v1392]) { Ok(v) => v, Err(e) => return Err(e) };
let v1394 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1395 = match s.literal(Lit::Numeral(v1394)) { Ok(v) => v, Err(e) => return Err(e) };
let v1396 = match s.builtin_core(EvalOp::Add, &[v1393, v1395]) { Ok(v) => v, Err(e) => return Err(e) };
let v1397 = match s.builtin_core(EvalOp::Extract, &[v1379, v1381, v1396]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1397)
}
Some(false) => {
let v1398 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1405 = match if_114_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1406 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1407 = match s.literal(Lit::Numeral(v1406)) { Ok(v) => v, Err(e) => return Err(e) };
let v1408 = match s.builtin_list(EvalOp::ListNth, &[v1398, v1405, v1407]) { Ok(v) => v, Err(e) => return Err(e) };
let v1409 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1410 = match s.literal(Lit::Numeral(v1409)) { Ok(v) => v, Err(e) => return Err(e) };
let v1411 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1418 = match if_115_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1419 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1420 = match s.literal(Lit::Numeral(v1419)) { Ok(v) => v, Err(e) => return Err(e) };
let v1421 = match s.builtin_list(EvalOp::ListNth, &[v1411, v1418, v1420]) { Ok(v) => v, Err(e) => return Err(e) };
let v1422 = match s.builtin_core(EvalOp::Length, &[v1421]) { Ok(v) => v, Err(e) => return Err(e) };
let v1423 = match s.builtin_core(EvalOp::Extract, &[v1408, v1410, v1422]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1423)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_117_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1307 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1308 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1364 = match if_111_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1365 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1308, v1364]) { Ok(v) => v, Err(e) => return Err(e) };
let v1366 = match eo__24str_5fflatten(s, v1365) { Ok(v) => v, Err(e) => return Err(e) };
let v1367 = match s.builtin_list(EvalOp::ListRev, &[v1307, v1366]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1367)
}
Some(false) => {
let v1368 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1424 = match if_116_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1425 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1368, v1424]) { Ok(v) => v, Err(e) => return Err(e) };
let v1426 = match eo__24str_5fflatten(s, v1425) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1426)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_118_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1431 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1432 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1433 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1432, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1434 = match s.builtin_list(EvalOp::ListRev, &[v1431, v1433]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1434)
}
Some(false) => {
let v1435 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1436 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1435, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1436)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_119_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1446 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1447 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1448 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1447, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1449 = match s.builtin_list(EvalOp::ListRev, &[v1446, v1448]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1449)
}
Some(false) => {
let v1450 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1451 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1450, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1451)
}
None => Ok(s.stuck()),
}
}
