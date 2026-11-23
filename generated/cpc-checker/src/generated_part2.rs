//! Generated functions, module 2 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
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
pub(super) fn case_34_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5for_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fcnf_5for_5fneg(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s: &mut Store, v5: Term, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s, v5, v14, v2, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_implies_pos"
pub fn eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s, a0);
s.leave();
result
}
pub(super) fn case_35_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fimplies_5fpos, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fimplies_5fpos(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_8_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_32_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_33_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_34_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_35_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s: &mut Store, v13: Term, v14: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s, v13, v14, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_implies_neg1"
pub fn eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s, a0);
s.leave();
result
}
pub(super) fn case_36_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fimplies_5fneg1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fimplies_5fneg1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s: &mut Store, v12: Term, v14: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s, v12, v14, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_implies_neg2"
pub fn eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s, a0);
s.leave();
result
}
pub(super) fn case_37_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fimplies_5fneg2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fimplies_5fneg2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s: &mut Store, v5: Term, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s, v5, v14, v2, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_equiv_pos1"
pub fn eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s, a0);
s.leave();
result
}
pub(super) fn case_38_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fequiv_5fpos1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fequiv_5fpos1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s: &mut Store, v14: Term, v5: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v15, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s, v14, v5, v2, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_equiv_pos2"
pub fn eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s, a0);
s.leave();
result
}
pub(super) fn case_39_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fequiv_5fpos2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fequiv_5fpos2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_9_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_36_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_37_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_38_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_39_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s: &mut Store, v14: Term, v2: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v11, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s, v14, v2, v13, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_equiv_neg1"
pub fn eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s, a0);
s.leave();
result
}
pub(super) fn case_40_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fequiv_5fneg1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fequiv_5fneg1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s: &mut Store, v12: Term, v14: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v15, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v11, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s, v12, v14, v2, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_equiv_neg2"
pub fn eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s, a0);
s.leave();
result
}
pub(super) fn case_41_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fequiv_5fneg2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fequiv_5fneg2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s: &mut Store, v14: Term, v5: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v13, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s, v14, v5, v2, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_xor_pos1"
pub fn eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s, a0);
s.leave();
result
}
pub(super) fn case_42_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fxor_5fpos1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fxor_5fpos1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s: &mut Store, v5: Term, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v13, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s, v5, v14, v2, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_xor_pos2"
pub fn eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s, a0);
s.leave();
result
}
pub(super) fn case_43_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fxor_5fpos2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fxor_5fpos2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_10_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_40_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_41_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_42_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_43_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s: &mut Store, v12: Term, v14: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v11, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s, v12, v14, v2, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_xor_neg1"
pub fn eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s, a0);
s.leave();
result
}
pub(super) fn case_44_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fxor_5fneg1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fxor_5fneg1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s: &mut Store, v2: Term, v14: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v13, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v11, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s, v2, v14, v13, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_xor_neg2"
pub fn eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s, a0);
s.leave();
result
}
pub(super) fn case_45_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fxor_5fneg2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fxor_5fneg2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1(s: &mut Store, v10: Term, v16: Term, v8: Term, v5: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v10, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1(s, v10, v16, v8, v5)
}
pub(super) fn body_eo__24eo_5fprog_5fcnf_5fite_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_cnf_ite_pos1"
pub fn eo__24eo_5fprog_5fcnf_5fite_5fpos1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fcnf_5fite_5fpos1(s, a0);
s.leave();
result
}
pub(super) fn case_46_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ecnf_5fite_5fpos1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fcnf_5fite_5fpos1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2(s: &mut Store, v10: Term, v16: Term, v8: Term, v2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v10, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
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
more_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2(s, v10, v16, v8, v2)
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
pub(super) fn cases_0_11_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_44_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_45_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_46_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_47_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_2_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_8_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_9_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_10_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_11_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3(s: &mut Store, v10: Term, v16: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v10, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
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
more_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3(s, v10, v16, v5, v2)
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
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1(s: &mut Store, v8: Term, v16: Term, v5: Term, v15: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v15, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
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
more_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1(s, v8, v16, v5, v15)
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
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2(s: &mut Store, v16: Term, v8: Term, v2: Term, v15: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v16, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v15, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
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
more_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2(s, v16, v8, v2, v15)
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
pub(super) fn more_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3(s: &mut Store, v5: Term, v16: Term, v2: Term, v15: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v15, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
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
more_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3(s, v5, v16, v2, v15)
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
pub(super) fn cases_0_12_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_48_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_49_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_50_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_51_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s: &mut Store, v34: Term, v9: Term, v31: Term, v2: Term, v30: Term, v15: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s: &mut Store, v20: Term, v22: Term, v21: Term, v12: Term, v2: Term, v15: Term, v9: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s, v34, v9, v31, v2, v30, v15)
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
more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite(s, v20, v22, v21, v12, v2, v15, v9)
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
pub(super) fn more_1_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s: &mut Store, v37: Term, v15: Term, v25: Term) -> CheckResult<Option<Term>> {
let v38 = match s.apply(v37, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s: &mut Store, v18: Term, v8: Term, v15: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s, v37, v15, v25)
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
more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5fcontra(s, v18, v8, v15)
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
pub(super) fn more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s: &mut Store, v15: Term, v12: Term, v9: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5farrays_5fread_5fover_5fwrite_5f1(s, v15, v12, v9, v18, v17)
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
pub(super) fn more_1_eo__24eo_5fprog_5farrays_5fext(s: &mut Store, v13: Term, v28: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v13, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5farrays_5fext(s: &mut Store, v11: Term, v8: Term, v16: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5farrays_5fext(s, v13, v28)
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
more_0_eo__24eo_5fprog_5farrays_5fext(s, v11, v8, v16, v14, v13)
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
pub(super) fn cases_0_13_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
match s.cached_program(ProgramId(952), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5ftrans(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(952), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(a0))
}
// EO program "$mk_cong_rhs"
pub fn eo__24mk_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(926), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fcong_5frhs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(926), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn cases_0_14_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_56_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_57_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_58_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_59_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_1_eo__24mk_5fnary_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
Ok(Some(a0))
}
// EO program "$mk_nary_cong_rhs"
pub fn eo__24mk_5fnary_5fcong_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(940), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fnary_5fcong_5frhs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(940), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_0_eo__24mk_5fnary_5fcong_5frhs(s, v2, v8, v20)
}
pub(super) fn more_0_eo__24mk_5fnary_5fcong_5frhs(s: &mut Store, v2: Term, v8: Term, v20: Term) -> CheckResult<Option<Term>> {
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
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
pub(super) fn cases_0_15_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_60_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_61_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_62_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_63_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_3_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_12_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_13_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_14_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_15_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_1_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_2_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_3_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
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
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
match s.cached_program(ProgramId(939), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fho_5fcong(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(939), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn more_0_eo__24mk_5fdistinct_5felim_5frec(s: &mut Store, v13: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
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
match s.cached_program(ProgramId(928), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdistinct_5felim_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(928), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_0_eo__24mk_5fdistinct_5felim_5frec(s, v13, v14)
}
pub(super) fn case_1_eo__24mk_5fdistinct_5felim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$mk_distinct_elim"
pub fn eo__24mk_5fdistinct_5felim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(927), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdistinct_5felim(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(927), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn cases_0_16_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_64_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_65_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_66_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_67_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdistinct_2dtrue(s: &mut Store, v14: Term, v15: Term, v9: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
pub(super) fn more_1_eo__24eo_5fprog_5fdistinct_2dtrue(s: &mut Store, v14: Term, v9: Term) -> CheckResult<Option<Term>> {
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match requires_0_eo__24eo_5fprog_5fdistinct_2dtrue(s, v14, v15, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
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
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v11 { return Ok(None); }
let v12 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24typed_5flist_5felement_5ftype(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24are_5fdistinct_5fterms_5flist(s, v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fdistinct_2dtrue(s, v14, v9)
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
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
pub(super) fn more_1_eo__24eo_5fprog_5fdistinct_2dfalse(s: &mut Store, v14: Term, v9: Term) -> CheckResult<Option<Term>> {
let v15 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match requires_0_eo__24eo_5fprog_5fdistinct_2dfalse(s, v14, v15, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
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
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSetof, &[v12, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[v13, v9]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fdistinct_2dfalse(s, v14, v9)
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
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(Next::Done(a1)))
}
pub(super) fn more_0_eo__24mk_5farith_5fsum_5fub_5frec(s: &mut Store, v22: Term, v9: Term, v15: Term, v11: Term, v17: Term, v21: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v23 = match s.apply(v22, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24arith_5frel_5fsum(s, v11, v17, v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v25])))
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
more_0_eo__24mk_5farith_5fsum_5fub_5frec(s, v22, v9, v15, v11, v17, v21, v2)
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
match s.cached_program(ProgramId(924), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5farith_5fsum_5fub_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(924), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn more_0_eo__24mk_5farith_5fsum_5fub(s: &mut Store, v13: Term, v18: Term, v12: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24mk_5farith_5fsum_5fub(s, v13, v18, v12)
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
pub(super) fn more_1_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_0_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v11: Term, v14: Term, v9: Term, v7: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24mk_5farith_5fmult_5fpos(s, v11, v14, v9, v7, a0, v2)
}
pub(super) fn more_3_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_2_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v11: Term, v14: Term, v9: Term, v7: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24mk_5farith_5fmult_5fpos(s, v11, v14, v9, v7, a0, v2)
}
pub(super) fn more_5_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_4_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v11: Term, v14: Term, v9: Term, v7: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
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
more_4_eo__24mk_5farith_5fmult_5fpos(s, v11, v14, v9, v7, a0, v2)
}
pub(super) fn more_7_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_6_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v11: Term, v14: Term, v9: Term, v7: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
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
more_7_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
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
more_6_eo__24mk_5farith_5fmult_5fpos(s, v11, v14, v9, v7, a0, v2)
}
pub(super) fn cases_0_0_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_9_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v17: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_8_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, v11: Term, v14: Term, v9: Term, v7: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
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
more_9_eo__24mk_5farith_5fmult_5fpos(s, v17, v26)
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
more_8_eo__24mk_5farith_5fmult_5fpos(s, v11, v14, v9, v7, a0, v2)
}
pub(super) fn cases_0_1_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_arith_mult_pos"
pub fn eo__24mk_5farith_5fmult_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5farith_5fmult_5fpos(s, a0, a1);
s.leave();
result
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_5fmult_5fpos(s: &mut Store, v7: Term, v11: Term, v0: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24mk_5farith_5fmult_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
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
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_5fmult_5fpos(s, v7, v11, v0, a0, a1)
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
pub(super) fn cases_0_17_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_68_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_69_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_70_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_71_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24mk_5farith_5fmult_5fneg(s: &mut Store, v15: Term, a0: Term, v2: Term, v4: Term, v14: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24mk_5farith_5fmult_5fneg(s, v15, a0, v2, v4, v14)
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
pub(super) fn more_0_eo__24eo_5fprog_5farith_5fmult_5fneg(s: &mut Store, v7: Term, v11: Term, v0: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24mk_5farith_5fmult_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
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
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_5fmult_5fneg(s, v7, v11, v0, a0, a1)
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
pub(super) fn more_4_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match eo__24eo_5fprog_5farith_5ftrichotomy(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
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
more_4_eo__24eo_5fcmd_5fstep_5fproven(s, v10, v12)
}
pub(super) fn if_0_eo__24greatest_5fint_5flt(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Add, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24greatest_5fint_5flt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::ToRat, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::Eq, &[v0, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24greatest_5fint_5flt(s, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
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
let v0 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::Add, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
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
pub(super) fn cases_0_18_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_72_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_73_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_74_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_75_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
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
pub(super) fn more_9_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a4: Term, a1: Term, a3: Term, v87: Term, v86: Term, v81: Term, v80: Term, v63: Term) -> CheckResult<Option<Term>> {
let v90 = match if_2_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v87, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v93, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v86, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v81, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v97, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v80, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v63, v100) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v101))
}
pub(super) fn more_8_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, v70: Term, v75: Term, v69: Term, v64: Term, a0: Term, a2: Term, a4: Term, a1: Term, a3: Term, v63: Term) -> CheckResult<Option<Term>> {
let v76 = match s.apply(v70, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_9_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a4, a1, a3, v87, v86, v81, v80, v63)
}
pub(super) fn more_7_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, v13: Term, v61: Term, v0: Term, a0: Term, a2: Term, a4: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_8_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, v70, v75, v69, v64, a0, a2, a4, a1, a3, v63)
}
pub(super) fn more_6_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, v25: Term, v49: Term, v14: Term, a2: Term, a3: Term, v13: Term, v0: Term, a0: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
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
more_7_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, v13, v61, v0, a0, a2, a4, a1, a3)
}
pub(super) fn more_5_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a3: Term, a0: Term, v37: Term, v36: Term, v25: Term, v14: Term, a2: Term, v13: Term, v0: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
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
more_6_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, v25, v49, v14, a2, a3, v13, v0, a0, a4, a1)
}
pub(super) fn more_4_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a2: Term, a1: Term, a3: Term, a0: Term, v25: Term, v14: Term, v13: Term, v0: Term, a4: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a3, a0, v37, v36, v25, v14, a2, v13, v0, a4, a1)
}
pub(super) fn more_3_eo__24eo_5fprog_5farith_5fmult_5ftangent(s: &mut Store, a3: Term, a0: Term, a2: Term, a1: Term, v13: Term, v0: Term, a4: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a2, a1, a3, a0, v25, v14, v13, v0, a4)
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
more_3_eo__24eo_5fprog_5farith_5fmult_5ftangent(s, a3, a0, a2, a1, v13, v0, a4)
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
match s.cached_program(ProgramId(1094), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24strip_5feven_5fexponent(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1094), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn requires_6_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v1: Term, v3: Term, a0: Term) -> CheckResult<Term> {
if v1 != v3 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_3_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.builtin_core(EvalOp::ToRat, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v3 = match s.literal(Lit::Rational(v2)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match requires_6_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v1, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$mk_arith_mult_sign_sgn"
pub fn eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(922), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(922), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_1_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v19, v16, v20, v13, a0, v2)
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
more_3_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v19, v12, v9, v16, a0, v2)
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
more_5_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v19, v12, v9, a0, v16, v2)
}
pub(super) fn requires_0_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v32: Term, v34: Term, v16: Term, v27: Term, a0: Term, v2: Term) -> CheckResult<Term> {
if v32 != v34 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v32) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v35 = match eo__24strip_5feven_5fexponent(s, v16, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, v2, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
pub(super) fn more_1_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v19: Term, v16: Term, v20: Term, v13: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
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
let v33 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v34 = match s.literal(Lit::Rational(v33)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match requires_0_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v32, v34, v16, v27, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn requires_2_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v21: Term, v23: Term, v12: Term, v16: Term, a0: Term, v2: Term) -> CheckResult<Term> {
if v21 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v21) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match eo__24strip_5feven_5fexponent(s, v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24mk_5farith_5fmult_5fsign_5fsgn(s, a0, v2, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn more_3_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v19: Term, v12: Term, v9: Term, v16: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
if v19 != v12 { return Ok(None); }
let v21 = match s.builtin_core(EvalOp::ToRat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v23 = match s.literal(Lit::Rational(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match requires_2_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v21, v23, v12, v16, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn requires_4_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v21: Term, v23: Term, a0: Term, v12: Term, v16: Term, v2: Term) -> CheckResult<Term> {
if v21 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v21) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match s.builtin_core(EvalOp::Not, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24strip_5feven_5fexponent(s, v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v24, v2, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn more_5_eo__24mk_5farith_5fmult_5fsign_5fsgn(s: &mut Store, v19: Term, v12: Term, v9: Term, a0: Term, v16: Term, v2: Term) -> CheckResult<Option<Term>> {
if v19 != v12 { return Ok(None); }
let v21 = match s.builtin_core(EvalOp::ToRat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v23 = match s.literal(Lit::Rational(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_4_eo__24mk_5farith_5fmult_5fsign_5fsgn(s, v21, v23, a0, v12, v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
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
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24to_5fcube(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
pub(super) fn more_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v19: Term, v23: Term, v35: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
pub(super) fn more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, a1: Term, v11: Term, v15: Term, v19: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
more_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v19, v23, v35, v2)
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
more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, a1, v11, v15, v19, v2)
}
pub(super) fn case_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
match s.cached_program(ProgramId(919), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(919), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_4_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v19, v16, v9, a1, v2)
}
pub(super) fn more_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v69: Term, v27: Term, v68: Term, v50: Term, v67: Term, v2: Term) -> CheckResult<Term> {
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
pub(super) fn requires_3_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v55: Term, v57: Term, v23: Term, v53: Term, v27: Term, v50: Term, v2: Term) -> CheckResult<Term> {
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
more_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v69, v27, v68, v50, v67, v2)
}
pub(super) fn more_6_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v42: Term, v23: Term, v53: Term, v27: Term, v50: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v55 = match s.builtin_core(EvalOp::ToRat, &[v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v57 = match s.literal(Lit::Rational(v56)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match requires_3_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v55, v57, v23, v53, v27, v50, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v78)))
}
pub(super) fn more_5_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v37: Term, v39: Term, v38: Term, v23: Term, v31: Term, a1: Term, v27: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
let v47 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v47 { return Ok(None); }
let v48 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
more_6_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v42, v23, v53, v27, v50, v2)
}
pub(super) fn more_4_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s: &mut Store, v19: Term, v16: Term, v9: Term, a1: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
more_5_eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v37, v39, v38, v23, v31, a1, v27, v2)
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
pub(super) fn more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, v19: Term, v16: Term, v20: Term, v2: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, v20, v31, v29, v2)
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
more_0_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, v19, v16, v20, v2)
}
pub(super) fn more_3_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, v20: Term, v31: Term, v29: Term, v2: Term) -> CheckResult<Option<Term>> {
let v32 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5ftypeof(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fnil(s, v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v31, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24mk_5farith_5fmult_5fabs_5fcomparison_5frec(s, v2, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn more_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s: &mut Store, v19: Term, v16: Term, v20: Term, v2: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, v20, v31, v29, v2)
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
more_2_eo__24mk_5farith_5fmult_5fabs_5fcomparison(s, v19, v16, v20, v2)
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
pub(super) fn cases_0_19_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_76_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_77_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_78_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_79_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_4_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_16_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_17_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_18_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_19_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
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
match s.cached_program(ProgramId(961), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fneg(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(961), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_0_eo__24poly_5fneg(s, v16, v17, v14, v2)
}
pub(super) fn more_0_eo__24poly_5fneg(s: &mut Store, v16: Term, v17: Term, v14: Term, v2: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24poly_5fneg(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn more_1_eo__24poly_5fadd(s: &mut Store, v61: Term, v68: Term) -> CheckResult<Term> {
let v69 = match s.apply(v61, v68) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v69)
}
pub(super) fn more_2_eo__24poly_5fadd(s: &mut Store, v48: Term, v55: Term) -> CheckResult<Term> {
let v56 = match s.apply(v48, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v56)
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
match s.cached_program(ProgramId(957), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fadd(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(957), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_5_eo__24poly_5fadd(s, v19, v12, v9, v2, v16)
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
pub(super) fn if_3_eo__24poly_5fadd(s: &mut Store, condition: Term, v12: Term, v9: Term, v26: Term, v23: Term, v16: Term, v2: Term) -> CheckResult<Term> {
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
more_2_eo__24poly_5fadd(s, v48, v55)
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
more_1_eo__24poly_5fadd(s, v61, v68)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24poly_5fadd(s: &mut Store, condition: Term, v9: Term, v23: Term, v2: Term, v16: Term, v12: Term, v26: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match s.builtin_core(EvalOp::Add, &[v9, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v31 = match s.literal(Lit::Rational(v30)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::Eq, &[v29, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_0_eo__24poly_5fadd(s, v32, v2, v16, v12, v9, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
Some(false) => {
let v43 = match s.builtin_core(EvalOp::Compare, &[v26, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match if_3_eo__24poly_5fadd(s, v43, v12, v9, v26, v23, v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24poly_5fadd(s: &mut Store, v19: Term, v12: Term, v9: Term, v2: Term, v16: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.builtin_core(EvalOp::Eq, &[v12, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match if_4_eo__24poly_5fadd(s, v28, v9, v23, v2, v16, v12, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v71))
}
pub(super) fn more_0_eo__24mon_5fmul_5fmon(s: &mut Store, v16: Term, v17: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
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
match s.cached_program(ProgramId(954), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mvar_5fmul_5fmvar(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(954), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_0_eo__24mon_5fmul_5fmon(s, v16, v17)
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
match s.cached_program(ProgramId(960), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fmul_5fmon(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(960), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
match s.cached_program(ProgramId(959), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fmul(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(959), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
let v10 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v11 = match s.literal(Lit::Rational(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Not, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, v26: Term, v38: Term) -> CheckResult<Term> {
let v39 = match s.apply(v26, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
pub(super) fn if_3_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v11 = match s.literal(Lit::Rational(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Not, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_4_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, v26: Term, v38: Term) -> CheckResult<Term> {
let v39 = match s.apply(v26, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
pub(super) fn case_6_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
Ok(Some(Next::Again([v2])))
}
pub(super) fn if_6_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
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
pub(super) fn if_7_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.builtin_core(EvalOp::ToRat, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v4 = match s.literal(Lit::Rational(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::IsEq, &[v2, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_6_eo__24get_5farith_5fpoly_5fnorm(s, v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
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
let v24 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
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
let v30 = match if_7_eo__24get_5farith_5fpoly_5fnorm(s, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v30)))
}
// EO program "$get_arith_poly_norm"
pub fn eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(891), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5farith_5fpoly_5fnorm(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(891), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
if let Some(found) = match cases_0_0_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
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
let v42 = match if_2_eo__24get_5farith_5fpoly_5fnorm(s, v15, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match if_3_eo__24get_5farith_5fpoly_5fnorm(s, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_5_eo__24get_5farith_5fpoly_5fnorm(s, v15, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v42)))
}
pub(super) fn cases_0_0_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_0_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_4_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24get_5farith_5fpoly_5fnorm(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_2_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
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
let v36 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v37 = match s.literal(Lit::Rational(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24get_5farith_5fpoly_5fnorm(s, v26, v38)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24get_5farith_5fpoly_5fnorm(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
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
let v36 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v37 = match s.literal(Lit::Rational(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24get_5farith_5fpoly_5fnorm(s, v26, v38)
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
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn case_1_eo__24is_5feq_5fmaybe_5fto_5freal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
if a1 != v2 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v72 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v67 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match requires_1_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v66, v67, v18, v15, v54, v11, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v81)
}
pub(super) fn if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
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
let v14 = match if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v14, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
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
let v14 = match if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v14, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
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
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
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
let v14 = match if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v14, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn cases_0_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.builtin_core(EvalOp::Neg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.builtin_core(EvalOp::Neg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
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
let v14 = match if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v14, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_poly_norm_rel_consts_rel"
pub fn eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, a0);
s.leave();
result
}
pub(super) fn more_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts(s: &mut Store, v17: Term, v15: Term) -> CheckResult<Option<Term>> {
let v18 = match eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::And, &[v15, v18]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.builtin_core(EvalOp::ToRat, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v8 = match s.literal(Lit::Rational(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Eq, &[v6, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToRat, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v12 = match s.literal(Lit::Rational(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Eq, &[v10, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Or, &[v9, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Not, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts(s, v17, v15)
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
let v62 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match requires_2_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v61, v62, v12, v9, v40, v18, v15, v54, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v82)
}
pub(super) fn more_5_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, v46: Term, v44: Term, v37: Term, v11: Term, v33: Term, v47: Term, v12: Term, v9: Term, v40: Term, v18: Term, v15: Term) -> CheckResult<Option<Term>> {
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
let v57 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v58 = match s.literal(Lit::Rational(v57)) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match requires_3_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v56, v58, v11, v33, v47, v12, v9, v40, v18, v15, v54) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v83))
}
pub(super) fn more_4_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s: &mut Store, v25: Term, v26: Term, v23: Term, v11: Term, v12: Term, v9: Term, v18: Term, v15: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v46, v44, v37, v11, v33, v47, v12, v9, v40, v18, v15)
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
more_4_eo__24eo_5fprog_5farith_5fpoly_5fnorm_5frel(s, v25, v26, v23, v11, v12, v9, v18, v15)
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
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2drepeat_2delim(s: &mut Store, v12: Term, v21: Term, v2: Term, v11: Term, v9: Term) -> CheckResult<Option<Term>> {
let v22 = match s.builtin_list(EvalOp::ListSingletonElim, &[v12, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match requires_1_eo__24eo_5fprog_5fbv_2drepeat_2delim(s, v22, v2, v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
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
more_2_eo__24eo_5fprog_5fbv_2drepeat_2delim(s, v12, v21, v2, v11, v9)
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v325: Term, v326: Term, v336: Term) -> CheckResult<Term> {
let v337 = match s.builtin_list(EvalOp::ListRepeat, &[v325, v326, v336]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match eo__24iota_5frec(s, v337, v338) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v339)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v323: Term, v324: Term, v12: Term) -> CheckResult<Term> {
if v323 != v324 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v323) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v325 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match eo__24bv_5fbitwidth(s, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.builtin_core(EvalOp::Add, &[v330, v331]) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.builtin_core(EvalOp::Add, &[v328, v332]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.builtin_core(EvalOp::Add, &[v327, v333]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.builtin_core(EvalOp::Add, &[v334, v335]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v325, v326, v336)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v634: Term, v635: Term, v645: Term) -> CheckResult<Term> {
let v646 = match s.builtin_list(EvalOp::ListRepeat, &[v634, v635, v645]) { Ok(v) => v, Err(e) => return Err(e) };
let v647 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v648 = match eo__24iota_5frec(s, v646, v647) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v648)
}
pub(super) fn requires_3_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v632: Term, v633: Term, v12: Term) -> CheckResult<Term> {
if v632 != v633 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v632) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v634 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v635 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v636 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v637 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v638 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v639 = match eo__24bv_5fbitwidth(s, v638) { Ok(v) => v, Err(e) => return Err(e) };
let v640 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v641 = match s.builtin_core(EvalOp::Add, &[v639, v640]) { Ok(v) => v, Err(e) => return Err(e) };
let v642 = match s.builtin_core(EvalOp::Add, &[v637, v641]) { Ok(v) => v, Err(e) => return Err(e) };
let v643 = match s.builtin_core(EvalOp::Add, &[v636, v642]) { Ok(v) => v, Err(e) => return Err(e) };
let v644 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v645 = match s.builtin_core(EvalOp::Add, &[v643, v644]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v634, v635, v645)
}
pub(super) fn more_45_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v346: Term, v657: Term, v124: Term) -> CheckResult<Term> {
let v658 = match s.apply(v346, v657) { Ok(v) => v, Err(e) => return Err(e) };
let v659 = match s.apply(v124, v658) { Ok(v) => v, Err(e) => return Err(e) };
let v660 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v661 = match s.apply(v659, v660) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v661)
}
pub(super) fn more_44_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v629: Term, v630: Term, v12: Term, v459: Term, v484: Term, v519: Term, v621: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v631 = match s.builtin_core(EvalOp::Add, &[v629, v630]) { Ok(v) => v, Err(e) => return Err(e) };
let v632 = match s.builtin_core(EvalOp::IsNeg, &[v631]) { Ok(v) => v, Err(e) => return Err(e) };
let v633 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v649 = match requires_3_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v632, v633, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v650 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v651 = match eo__24bv_5fbitwidth(s, v650) { Ok(v) => v, Err(e) => return Err(e) };
let v652 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v653 = match s.builtin_core(EvalOp::Add, &[v651, v652]) { Ok(v) => v, Err(e) => return Err(e) };
let v654 = match eo__24bv_5fsmulo_5felim_5frec(s, v459, v484, v519, v621, v649, v653) { Ok(v) => v, Err(e) => return Err(e) };
let v655 = match eo__24eo_5ftypeof(s, v654) { Ok(v) => v, Err(e) => return Err(e) };
let v656 = match eo__24eo_5fnil(s, v434, v655) { Ok(v) => v, Err(e) => return Err(e) };
let v657 = match s.apply(v433, v656) { Ok(v) => v, Err(e) => return Err(e) };
more_45_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v346, v657, v124)
}
pub(super) fn more_43_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v588: Term, v618: Term, v587: Term, v550: Term, v12: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v619 = match eo__24eo_5fnil(s, v588, v618) { Ok(v) => v, Err(e) => return Err(e) };
let v620 = match s.apply(v587, v619) { Ok(v) => v, Err(e) => return Err(e) };
let v621 = match s.apply(v550, v620) { Ok(v) => v, Err(e) => return Err(e) };
let v622 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v623 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v624 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v625 = match eo__24bv_5fbitwidth(s, v624) { Ok(v) => v, Err(e) => return Err(e) };
let v626 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v627 = match s.builtin_core(EvalOp::Add, &[v625, v626]) { Ok(v) => v, Err(e) => return Err(e) };
let v628 = match s.builtin_core(EvalOp::Add, &[v623, v627]) { Ok(v) => v, Err(e) => return Err(e) };
let v629 = match s.builtin_core(EvalOp::Add, &[v622, v628]) { Ok(v) => v, Err(e) => return Err(e) };
let v630 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_44_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v629, v630, v12, v459, v484, v519, v621, v434, v433, v346, v124)
}
pub(super) fn more_42_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v605: Term, v606: Term, v603: Term, v9: Term, v599: Term, v594: Term, v593: Term, v591: Term, v588: Term, v587: Term, v550: Term, v12: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v607 = match s.builtin_core(EvalOp::Add, &[v605, v606]) { Ok(v) => v, Err(e) => return Err(e) };
let v608 = match s.construct(Constructor::eo_extract, &[v603, v607]) { Ok(v) => v, Err(e) => return Err(e) };
let v609 = match s.apply(v608, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v610 = match s.apply(v599, v609) { Ok(v) => v, Err(e) => return Err(e) };
let v611 = match s.apply(v594, v610) { Ok(v) => v, Err(e) => return Err(e) };
let v612 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v613 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v614 = match eo__24eo_5fnil(s, v612, v613) { Ok(v) => v, Err(e) => return Err(e) };
let v615 = match s.apply(v611, v614) { Ok(v) => v, Err(e) => return Err(e) };
let v616 = match s.apply(v593, v615) { Ok(v) => v, Err(e) => return Err(e) };
let v617 = match s.apply(v591, v616) { Ok(v) => v, Err(e) => return Err(e) };
let v618 = match eo__24eo_5ftypeof(s, v617) { Ok(v) => v, Err(e) => return Err(e) };
more_43_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v588, v618, v587, v550, v12, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_41_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v9: Term, v594: Term, v593: Term, v591: Term, v588: Term, v587: Term, v550: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v595 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v596 = match eo__24bv_5fbitwidth(s, v595) { Ok(v) => v, Err(e) => return Err(e) };
let v597 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v598 = match s.builtin_core(EvalOp::Add, &[v596, v597]) { Ok(v) => v, Err(e) => return Err(e) };
let v599 = match s.construct(Constructor::eo_sign_5fextend, &[v598]) { Ok(v) => v, Err(e) => return Err(e) };
let v600 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v601 = match eo__24bv_5fbitwidth(s, v600) { Ok(v) => v, Err(e) => return Err(e) };
let v602 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v603 = match s.builtin_core(EvalOp::Add, &[v601, v602]) { Ok(v) => v, Err(e) => return Err(e) };
let v604 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v605 = match eo__24bv_5fbitwidth(s, v604) { Ok(v) => v, Err(e) => return Err(e) };
let v606 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_42_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v605, v606, v603, v9, v599, v594, v593, v591, v588, v587, v550, v12, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_40_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v581: Term, v582: Term, v580: Term, v562: Term, v560: Term, v551: Term, v9: Term, v12: Term, v550: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v583 = match eo__24eo_5fnil(s, v581, v582) { Ok(v) => v, Err(e) => return Err(e) };
let v584 = match s.apply(v580, v583) { Ok(v) => v, Err(e) => return Err(e) };
let v585 = match s.apply(v562, v584) { Ok(v) => v, Err(e) => return Err(e) };
let v586 = match s.apply(v560, v585) { Ok(v) => v, Err(e) => return Err(e) };
let v587 = match s.apply(v551, v586) { Ok(v) => v, Err(e) => return Err(e) };
let v588 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v589 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v590 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v591 = match s.construct(Constructor::eo_extract, &[v589, v590]) { Ok(v) => v, Err(e) => return Err(e) };
let v592 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v593 = match s.apply(v592, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v594 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_41_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v9, v594, v593, v591, v588, v587, v550, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_39_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v570: Term, v12: Term, v568: Term, v563: Term, v562: Term, v560: Term, v551: Term, v9: Term, v550: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v571 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v572 = match s.builtin_core(EvalOp::Add, &[v570, v571]) { Ok(v) => v, Err(e) => return Err(e) };
let v573 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v574 = match eo__24bv_5fbitwidth(s, v573) { Ok(v) => v, Err(e) => return Err(e) };
let v575 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v576 = match s.builtin_core(EvalOp::Add, &[v574, v575]) { Ok(v) => v, Err(e) => return Err(e) };
let v577 = match s.construct(Constructor::eo_extract, &[v572, v576]) { Ok(v) => v, Err(e) => return Err(e) };
let v578 = match s.apply(v577, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v579 = match s.apply(v568, v578) { Ok(v) => v, Err(e) => return Err(e) };
let v580 = match s.apply(v563, v579) { Ok(v) => v, Err(e) => return Err(e) };
let v581 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v582 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_40_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v581, v582, v580, v562, v560, v551, v9, v12, v550, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_38_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v557: Term, v558: Term, v555: Term, v12: Term, v551: Term, v9: Term, v550: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v559 = match s.builtin_core(EvalOp::Add, &[v557, v558]) { Ok(v) => v, Err(e) => return Err(e) };
let v560 = match s.construct(Constructor::eo_extract, &[v555, v559]) { Ok(v) => v, Err(e) => return Err(e) };
let v561 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v562 = match s.apply(v561, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v563 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v564 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v565 = match eo__24bv_5fbitwidth(s, v564) { Ok(v) => v, Err(e) => return Err(e) };
let v566 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v567 = match s.builtin_core(EvalOp::Add, &[v565, v566]) { Ok(v) => v, Err(e) => return Err(e) };
let v568 = match s.construct(Constructor::eo_sign_5fextend, &[v567]) { Ok(v) => v, Err(e) => return Err(e) };
let v569 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v570 = match eo__24bv_5fbitwidth(s, v569) { Ok(v) => v, Err(e) => return Err(e) };
more_39_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v570, v12, v568, v563, v562, v560, v551, v9, v550, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_37_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v543: Term, v546: Term, v525: Term, v523: Term, v520: Term, v12: Term, v9: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v547 = match s.apply(v543, v546) { Ok(v) => v, Err(e) => return Err(e) };
let v548 = match s.apply(v525, v547) { Ok(v) => v, Err(e) => return Err(e) };
let v549 = match s.apply(v523, v548) { Ok(v) => v, Err(e) => return Err(e) };
let v550 = match s.apply(v520, v549) { Ok(v) => v, Err(e) => return Err(e) };
let v551 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v552 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v553 = match eo__24bv_5fbitwidth(s, v552) { Ok(v) => v, Err(e) => return Err(e) };
let v554 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v555 = match s.builtin_core(EvalOp::Add, &[v553, v554]) { Ok(v) => v, Err(e) => return Err(e) };
let v556 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v557 = match eo__24bv_5fbitwidth(s, v556) { Ok(v) => v, Err(e) => return Err(e) };
let v558 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_38_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v557, v558, v555, v12, v551, v9, v550, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_36_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v533: Term, v534: Term, v12: Term, v9: Term, v531: Term, v526: Term, v525: Term, v523: Term, v520: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v535 = match s.builtin_core(EvalOp::Add, &[v533, v534]) { Ok(v) => v, Err(e) => return Err(e) };
let v536 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v537 = match eo__24bv_5fbitwidth(s, v536) { Ok(v) => v, Err(e) => return Err(e) };
let v538 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v539 = match s.builtin_core(EvalOp::Add, &[v537, v538]) { Ok(v) => v, Err(e) => return Err(e) };
let v540 = match s.construct(Constructor::eo_extract, &[v535, v539]) { Ok(v) => v, Err(e) => return Err(e) };
let v541 = match s.apply(v540, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v542 = match s.apply(v531, v541) { Ok(v) => v, Err(e) => return Err(e) };
let v543 = match s.apply(v526, v542) { Ok(v) => v, Err(e) => return Err(e) };
let v544 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v545 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v546 = match eo__24eo_5fnil(s, v544, v545) { Ok(v) => v, Err(e) => return Err(e) };
more_37_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v543, v546, v525, v523, v520, v12, v9, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_35_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v521: Term, v522: Term, v9: Term, v12: Term, v520: Term, v459: Term, v484: Term, v519: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v523 = match s.construct(Constructor::eo_extract, &[v521, v522]) { Ok(v) => v, Err(e) => return Err(e) };
let v524 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v525 = match s.apply(v524, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v526 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v527 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v528 = match eo__24bv_5fbitwidth(s, v527) { Ok(v) => v, Err(e) => return Err(e) };
let v529 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v530 = match s.builtin_core(EvalOp::Add, &[v528, v529]) { Ok(v) => v, Err(e) => return Err(e) };
let v531 = match s.construct(Constructor::eo_sign_5fextend, &[v530]) { Ok(v) => v, Err(e) => return Err(e) };
let v532 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v533 = match eo__24bv_5fbitwidth(s, v532) { Ok(v) => v, Err(e) => return Err(e) };
let v534 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_36_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v533, v534, v12, v9, v531, v526, v525, v523, v520, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_34_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v510: Term, v12: Term, v501: Term, v496: Term, v495: Term, v493: Term, v9: Term, v459: Term, v484: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v511 = match s.apply(v510, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v512 = match s.apply(v501, v511) { Ok(v) => v, Err(e) => return Err(e) };
let v513 = match s.apply(v496, v512) { Ok(v) => v, Err(e) => return Err(e) };
let v514 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v515 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v516 = match eo__24eo_5fnil(s, v514, v515) { Ok(v) => v, Err(e) => return Err(e) };
let v517 = match s.apply(v513, v516) { Ok(v) => v, Err(e) => return Err(e) };
let v518 = match s.apply(v495, v517) { Ok(v) => v, Err(e) => return Err(e) };
let v519 = match s.apply(v493, v518) { Ok(v) => v, Err(e) => return Err(e) };
let v520 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v521 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v522 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_35_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v521, v522, v9, v12, v520, v459, v484, v519, v434, v433, v346, v124)
}
pub(super) fn more_33_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v498: Term, v12: Term, v496: Term, v495: Term, v493: Term, v9: Term, v459: Term, v484: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v499 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v500 = match s.builtin_core(EvalOp::Add, &[v498, v499]) { Ok(v) => v, Err(e) => return Err(e) };
let v501 = match s.construct(Constructor::eo_sign_5fextend, &[v500]) { Ok(v) => v, Err(e) => return Err(e) };
let v502 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v503 = match eo__24bv_5fbitwidth(s, v502) { Ok(v) => v, Err(e) => return Err(e) };
let v504 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v505 = match s.builtin_core(EvalOp::Add, &[v503, v504]) { Ok(v) => v, Err(e) => return Err(e) };
let v506 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v507 = match eo__24bv_5fbitwidth(s, v506) { Ok(v) => v, Err(e) => return Err(e) };
let v508 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v509 = match s.builtin_core(EvalOp::Add, &[v507, v508]) { Ok(v) => v, Err(e) => return Err(e) };
let v510 = match s.construct(Constructor::eo_extract, &[v505, v509]) { Ok(v) => v, Err(e) => return Err(e) };
more_34_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v510, v12, v501, v496, v495, v493, v9, v459, v484, v434, v433, v346, v124)
}
pub(super) fn more_32_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v486: Term, v12: Term, v9: Term, v459: Term, v484: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v487 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v488 = match s.builtin_core(EvalOp::Add, &[v486, v487]) { Ok(v) => v, Err(e) => return Err(e) };
let v489 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v490 = match eo__24bv_5fbitwidth(s, v489) { Ok(v) => v, Err(e) => return Err(e) };
let v491 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v492 = match s.builtin_core(EvalOp::Add, &[v490, v491]) { Ok(v) => v, Err(e) => return Err(e) };
let v493 = match s.construct(Constructor::eo_extract, &[v488, v492]) { Ok(v) => v, Err(e) => return Err(e) };
let v494 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v495 = match s.apply(v494, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v496 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v497 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v498 = match eo__24bv_5fbitwidth(s, v497) { Ok(v) => v, Err(e) => return Err(e) };
more_33_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v498, v12, v496, v495, v493, v9, v459, v484, v434, v433, v346, v124)
}
pub(super) fn more_31_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v473: Term, v474: Term, v471: Term, v9: Term, v467: Term, v462: Term, v461: Term, v12: Term, v459: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v475 = match s.builtin_core(EvalOp::Add, &[v473, v474]) { Ok(v) => v, Err(e) => return Err(e) };
let v476 = match s.construct(Constructor::eo_extract, &[v471, v475]) { Ok(v) => v, Err(e) => return Err(e) };
let v477 = match s.apply(v476, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v478 = match s.apply(v467, v477) { Ok(v) => v, Err(e) => return Err(e) };
let v479 = match s.apply(v462, v478) { Ok(v) => v, Err(e) => return Err(e) };
let v480 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v481 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v482 = match eo__24eo_5fnil(s, v480, v481) { Ok(v) => v, Err(e) => return Err(e) };
let v483 = match s.apply(v479, v482) { Ok(v) => v, Err(e) => return Err(e) };
let v484 = match s.apply(v461, v483) { Ok(v) => v, Err(e) => return Err(e) };
let v485 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v486 = match eo__24bv_5fbitwidth(s, v485) { Ok(v) => v, Err(e) => return Err(e) };
more_32_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v486, v12, v9, v459, v484, v434, v433, v346, v124)
}
pub(super) fn more_30_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v9: Term, v462: Term, v461: Term, v459: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v463 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match eo__24bv_5fbitwidth(s, v463) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.builtin_core(EvalOp::Add, &[v464, v465]) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match s.construct(Constructor::eo_sign_5fextend, &[v466]) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match eo__24bv_5fbitwidth(s, v468) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v471 = match s.builtin_core(EvalOp::Add, &[v469, v470]) { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v473 = match eo__24bv_5fbitwidth(s, v472) { Ok(v) => v, Err(e) => return Err(e) };
let v474 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v473, v474, v471, v9, v467, v462, v461, v12, v459, v434, v433, v346, v124)
}
pub(super) fn more_29_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v446: Term, v450: Term, v12: Term, v442: Term, v437: Term, v436: Term, v9: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v451 = match s.construct(Constructor::eo_extract, &[v446, v450]) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match s.apply(v451, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.apply(v442, v452) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match s.apply(v437, v453) { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match eo__24eo_5fnil(s, v455, v456) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.apply(v454, v457) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match s.apply(v436, v458) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v461 = match s.apply(v460, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v9, v462, v461, v459, v434, v433, v346, v124)
}
pub(super) fn more_28_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v438: Term, v12: Term, v437: Term, v436: Term, v9: Term, v434: Term, v433: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v439 = match eo__24bv_5fbitwidth(s, v438) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.builtin_core(EvalOp::Add, &[v439, v440]) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match s.construct(Constructor::eo_sign_5fextend, &[v441]) { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v444 = match eo__24bv_5fbitwidth(s, v443) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match s.builtin_core(EvalOp::Add, &[v444, v445]) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v448 = match eo__24bv_5fbitwidth(s, v447) { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match s.builtin_core(EvalOp::Add, &[v448, v449]) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v446, v450, v12, v442, v437, v436, v9, v434, v433, v346, v124)
}
pub(super) fn more_27_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v414: Term, v426: Term, v409: Term, v404: Term, v403: Term, v373: Term, v347: Term, v12: Term, v9: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v427 = match s.apply(v414, v426) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.apply(v409, v427) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match eo__24eo_5ftypeof(s, v428) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match eo__24eo_5fnil(s, v404, v429) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.apply(v403, v430) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match s.apply(v373, v431) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.apply(v347, v432) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.apply(v435, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v438, v12, v437, v436, v9, v434, v433, v346, v124)
}
pub(super) fn more_26_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v9: Term, v12: Term, v414: Term, v409: Term, v404: Term, v403: Term, v373: Term, v347: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v415 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.construct(Constructor::eo_sign_5fextend, &[v416]) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.apply(v417, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.apply(v415, v418) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match s.construct(Constructor::eo_sign_5fextend, &[v421]) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.apply(v422, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match eo__24eo_5ftypeof(s, v423) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match eo__24eo_5fnil(s, v420, v424) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.apply(v419, v425) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v414, v426, v409, v404, v403, v373, v347, v12, v9, v346, v124)
}
pub(super) fn more_25_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v374: Term, v402: Term, v12: Term, v9: Term, v373: Term, v347: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v403 = match s.apply(v374, v402) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match eo__24bv_5fbitwidth(s, v405) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match eo__24bv_5fbitwidth(s, v407) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.construct(Constructor::eo_extract, &[v406, v408]) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.construct(Constructor::eo_sign_5fextend, &[v411]) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.apply(v412, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.apply(v410, v413) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v9, v12, v414, v409, v404, v403, v373, v347, v346, v124)
}
pub(super) fn more_24_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v390: Term, v9: Term, v389: Term, v12: Term, v388: Term, v383: Term, v374: Term, v373: Term, v347: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v391 = match s.construct(Constructor::eo_sign_5fextend, &[v390]) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.apply(v391, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.apply(v389, v392) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.construct(Constructor::eo_sign_5fextend, &[v395]) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v396, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match eo__24eo_5ftypeof(s, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match eo__24eo_5fnil(s, v394, v398) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.apply(v393, v399) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.apply(v388, v400) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.apply(v383, v401) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v374, v402, v12, v9, v373, v347, v346, v124)
}
pub(super) fn more_23_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v378: Term, v9: Term, v374: Term, v373: Term, v347: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v379 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match eo__24bv_5fbitwidth(s, v379) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.builtin_core(EvalOp::Add, &[v380, v381]) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.construct(Constructor::eo_extract, &[v378, v382]) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.construct(Constructor::eo_sign_5fextend, &[v385]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.apply(v386, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.apply(v384, v387) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v390, v9, v389, v12, v388, v383, v374, v373, v347, v346, v124)
}
pub(super) fn more_22_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v366: Term, v12: Term, v364: Term, v363: Term, v358: Term, v353: Term, v348: Term, v9: Term, v347: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v367 = match s.apply(v366, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match eo__24eo_5ftypeof(s, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match eo__24eo_5fnil(s, v364, v368) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.apply(v363, v369) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.apply(v358, v370) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.apply(v353, v371) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v348, v372) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match eo__24bv_5fbitwidth(s, v375) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.builtin_core(EvalOp::Add, &[v376, v377]) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v378, v9, v374, v373, v347, v346, v124)
}
pub(super) fn more_21_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v354: Term, v9: Term, v353: Term, v348: Term, v347: Term, v346: Term, v124: Term) -> CheckResult<Term> {
let v355 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.construct(Constructor::eo_sign_5fextend, &[v355]) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.apply(v356, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.apply(v354, v357) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.construct(Constructor::eo_sign_5fextend, &[v360]) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.apply(v361, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.apply(v359, v362) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.construct(Constructor::eo_sign_5fextend, &[v365]) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v366, v12, v364, v363, v358, v353, v348, v9, v347, v346, v124)
}
pub(super) fn more_20_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v342: Term, v150: Term, v175: Term, v210: Term, v312: Term, v340: Term, v125: Term, v12: Term, v9: Term, v124: Term) -> CheckResult<Term> {
let v343 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.builtin_core(EvalOp::Add, &[v342, v343]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match eo__24bv_5fsmulo_5felim_5frec(s, v150, v175, v210, v312, v340, v344) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.apply(v125, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match eo__24bv_5fbitwidth(s, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match eo__24bv_5fbitwidth(s, v351) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.construct(Constructor::eo_extract, &[v350, v352]) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v354, v9, v353, v348, v347, v346, v124)
}
pub(super) fn more_19_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v315: Term, v314: Term, v313: Term, v12: Term, v150: Term, v175: Term, v210: Term, v312: Term, v125: Term, v9: Term, v124: Term) -> CheckResult<Term> {
let v316 = match eo__24bv_5fbitwidth(s, v315) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.builtin_core(EvalOp::Add, &[v316, v317]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.builtin_core(EvalOp::Add, &[v314, v318]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.builtin_core(EvalOp::Add, &[v313, v319]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.builtin_core(EvalOp::Add, &[v320, v321]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.builtin_core(EvalOp::IsNeg, &[v322]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match requires_1_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v323, v324, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match eo__24bv_5fbitwidth(s, v341) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v342, v150, v175, v210, v312, v340, v125, v12, v9, v124)
}
pub(super) fn more_18_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v9: Term, v303: Term, v302: Term, v284: Term, v282: Term, v279: Term, v278: Term, v241: Term, v12: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v304 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match eo__24eo_5fnil(s, v303, v304) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v302, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v284, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.apply(v282, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match eo__24eo_5ftypeof(s, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match eo__24eo_5fnil(s, v279, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v278, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v241, v311) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v315, v314, v313, v12, v150, v175, v210, v312, v125, v9, v124)
}
pub(super) fn more_17_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v291: Term, v12: Term, v9: Term, v290: Term, v285: Term, v284: Term, v282: Term, v279: Term, v278: Term, v241: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v292 = match eo__24bv_5fbitwidth(s, v291) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.builtin_core(EvalOp::Add, &[v292, v293]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match eo__24bv_5fbitwidth(s, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.builtin_core(EvalOp::Add, &[v296, v297]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo_extract, &[v294, v298]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v299, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v290, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v285, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v9, v303, v302, v284, v282, v279, v278, v241, v12, v150, v175, v210, v125, v124)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v9: Term, v12: Term, v279: Term, v278: Term, v241: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v280 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo_extract, &[v280, v281]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.apply(v283, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match eo__24bv_5fbitwidth(s, v286) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.builtin_core(EvalOp::Add, &[v287, v288]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.construct(Constructor::eo_sign_5fextend, &[v289]) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v291, v12, v9, v290, v285, v284, v282, v279, v278, v241, v150, v175, v210, v125, v124)
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v263: Term, v267: Term, v12: Term, v259: Term, v254: Term, v253: Term, v251: Term, v242: Term, v9: Term, v241: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v268 = match s.construct(Constructor::eo_extract, &[v263, v267]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v268, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v259, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v254, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match eo__24eo_5fnil(s, v272, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v271, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v253, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v251, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v242, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v9, v12, v279, v278, v241, v150, v175, v210, v125, v124)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v255: Term, v12: Term, v254: Term, v253: Term, v251: Term, v242: Term, v9: Term, v241: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v256 = match eo__24bv_5fbitwidth(s, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.builtin_core(EvalOp::Add, &[v256, v257]) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.construct(Constructor::eo_sign_5fextend, &[v258]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match eo__24bv_5fbitwidth(s, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.builtin_core(EvalOp::Add, &[v261, v262]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match eo__24bv_5fbitwidth(s, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.builtin_core(EvalOp::Add, &[v265, v266]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v263, v267, v12, v259, v254, v253, v251, v242, v9, v241, v150, v175, v210, v125, v124)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v243: Term, v12: Term, v242: Term, v9: Term, v241: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v244 = match eo__24bv_5fbitwidth(s, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.builtin_core(EvalOp::Add, &[v244, v245]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match eo__24bv_5fbitwidth(s, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.builtin_core(EvalOp::Add, &[v248, v249]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.construct(Constructor::eo_extract, &[v246, v250]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v252, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v255, v12, v254, v253, v251, v242, v9, v241, v150, v175, v210, v125, v124)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v231: Term, v9: Term, v222: Term, v217: Term, v216: Term, v214: Term, v211: Term, v12: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v232 = match s.apply(v231, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v222, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v217, v233) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match eo__24eo_5fnil(s, v235, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v234, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v216, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v214, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v211, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v243, v12, v242, v9, v241, v150, v175, v210, v125, v124)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v219: Term, v12: Term, v9: Term, v217: Term, v216: Term, v214: Term, v211: Term, v150: Term, v175: Term, v210: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v220 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.builtin_core(EvalOp::Add, &[v219, v220]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_sign_5fextend, &[v221]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match eo__24bv_5fbitwidth(s, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_core(EvalOp::Add, &[v224, v225]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match eo__24bv_5fbitwidth(s, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.builtin_core(EvalOp::Add, &[v228, v229]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_extract, &[v226, v230]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v231, v9, v222, v217, v216, v214, v211, v12, v150, v175, v210, v125, v124)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v204: Term, v207: Term, v186: Term, v184: Term, v9: Term, v12: Term, v150: Term, v175: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v208 = match s.apply(v204, v207) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v186, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v184, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_extract, &[v212, v213]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v215, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match eo__24bv_5fbitwidth(s, v218) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v219, v12, v9, v217, v216, v214, v211, v150, v175, v210, v125, v124)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v194: Term, v195: Term, v12: Term, v192: Term, v187: Term, v186: Term, v184: Term, v9: Term, v150: Term, v175: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v196 = match s.builtin_core(EvalOp::Add, &[v194, v195]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match eo__24bv_5fbitwidth(s, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.builtin_core(EvalOp::Add, &[v198, v199]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_extract, &[v196, v200]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v201, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v192, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v187, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match eo__24eo_5fnil(s, v205, v206) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v204, v207, v186, v184, v9, v12, v150, v175, v125, v124)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v179: Term, v183: Term, v12: Term, v9: Term, v150: Term, v175: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v184 = match s.construct(Constructor::eo_extract, &[v179, v183]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v185, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match eo__24bv_5fbitwidth(s, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.builtin_core(EvalOp::Add, &[v189, v190]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_sign_5fextend, &[v191]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match eo__24bv_5fbitwidth(s, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v194, v195, v12, v192, v187, v186, v184, v9, v150, v175, v125, v124)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v9: Term, v171: Term, v170: Term, v152: Term, v12: Term, v150: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v172 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match eo__24eo_5fnil(s, v171, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v170, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v152, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match eo__24bv_5fbitwidth(s, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_core(EvalOp::Add, &[v177, v178]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match eo__24bv_5fbitwidth(s, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.builtin_core(EvalOp::Add, &[v181, v182]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v179, v183, v12, v9, v150, v175, v125, v124)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v159: Term, v12: Term, v9: Term, v158: Term, v153: Term, v152: Term, v150: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v160 = match eo__24bv_5fbitwidth(s, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_core(EvalOp::Add, &[v160, v161]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match eo__24bv_5fbitwidth(s, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.builtin_core(EvalOp::Add, &[v164, v165]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo_extract, &[v162, v166]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v167, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v158, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v153, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v9, v171, v170, v152, v12, v150, v125, v124)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v146: Term, v147: Term, v145: Term, v127: Term, v9: Term, v12: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v148 = match eo__24eo_5fnil(s, v146, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v145, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v127, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v151, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match eo__24bv_5fbitwidth(s, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.builtin_core(EvalOp::Add, &[v155, v156]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_sign_5fextend, &[v157]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v159, v12, v9, v158, v153, v152, v150, v125, v124)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v135: Term, v12: Term, v133: Term, v128: Term, v127: Term, v9: Term, v125: Term, v124: Term) -> CheckResult<Term> {
let v136 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_core(EvalOp::Add, &[v135, v136]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match eo__24bv_5fbitwidth(s, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_core(EvalOp::Add, &[v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_extract, &[v137, v141]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v142, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v133, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v128, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v146, v147, v145, v127, v9, v12, v125, v124)
}
pub(super) fn more_52_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v91: Term, v118: Term, v61: Term, v35: Term) -> CheckResult<Term> {
let v119 = match s.apply(v91, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v61, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v35, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v121, v122) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v123)
}
pub(super) fn more_51_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v103: Term, v106: Term, v12: Term, v102: Term, v97: Term, v92: Term, v91: Term, v61: Term, v35: Term) -> CheckResult<Term> {
let v107 = match s.apply(v103, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_sign_5fextend, &[v109]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24eo_5ftypeof(s, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match eo__24eo_5fnil(s, v108, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v107, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v102, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v97, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match eo__24eo_5ftypeof(s, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match eo__24eo_5fnil(s, v92, v117) { Ok(v) => v, Err(e) => return Err(e) };
more_52_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v91, v118, v61, v35)
}
pub(super) fn more_50_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v94: Term, v9: Term, v92: Term, v91: Term, v61: Term, v35: Term) -> CheckResult<Term> {
let v95 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match eo__24bv_5fbitwidth(s, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_extract, &[v94, v96]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_sign_5fextend, &[v99]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v100, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v98, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_sign_5fextend, &[v104]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v9) { Ok(v) => v, Err(e) => return Err(e) };
more_51_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v103, v106, v12, v102, v97, v92, v91, v61, v35)
}
pub(super) fn more_49_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v12: Term, v82: Term, v81: Term, v76: Term, v71: Term, v62: Term, v9: Term, v61: Term, v35: Term) -> CheckResult<Term> {
let v83 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_sign_5fextend, &[v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24eo_5ftypeof(s, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24eo_5fnil(s, v82, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v81, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v76, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v71, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v62, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match eo__24bv_5fbitwidth(s, v93) { Ok(v) => v, Err(e) => return Err(e) };
more_50_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v94, v9, v92, v91, v61, v35)
}
pub(super) fn more_48_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v66: Term, v70: Term, v12: Term, v9: Term, v62: Term, v61: Term, v35: Term) -> CheckResult<Term> {
let v71 = match s.construct(Constructor::eo_extract, &[v66, v70]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_sign_5fextend, &[v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v72, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_sign_5fextend, &[v78]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v77, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_49_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v12, v82, v81, v76, v71, v62, v9, v61, v35)
}
pub(super) fn more_47_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v46: Term, v58: Term, v41: Term, v36: Term, v12: Term, v9: Term, v35: Term) -> CheckResult<Term> {
let v59 = match s.apply(v46, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v41, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v36, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match eo__24bv_5fbitwidth(s, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_core(EvalOp::Add, &[v64, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24bv_5fbitwidth(s, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_core(EvalOp::Add, &[v68, v69]) { Ok(v) => v, Err(e) => return Err(e) };
more_48_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v66, v70, v12, v9, v62, v61, v35)
}
pub(super) fn more_46_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v9: Term, v12: Term, v46: Term, v41: Term, v36: Term, v35: Term) -> CheckResult<Term> {
let v47 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_sign_5fextend, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v47, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_sign_5fextend, &[v53]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24eo_5ftypeof(s, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match eo__24eo_5fnil(s, v52, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v51, v57) { Ok(v) => v, Err(e) => return Err(e) };
more_47_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v46, v58, v41, v36, v12, v9, v35)
}
pub(super) fn if_53_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, condition: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24bv_5fbitwidth(s, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24bv_5fbitwidth(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_extract, &[v38, v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_sign_5fextend, &[v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v42, v45) { Ok(v) => v, Err(e) => return Err(e) };
more_46_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v9, v12, v46, v41, v36, v35)
}
Some(false) => {
let v124 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match eo__24bv_5fbitwidth(s, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_core(EvalOp::Add, &[v130, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_sign_5fextend, &[v132]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match eo__24bv_5fbitwidth(s, v134) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v135, v12, v133, v128, v127, v9, v125, v124)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_54_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v28: Term, v29: Term) -> CheckResult<Term> {
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
pub(super) fn if_55_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, condition: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fnil(s, v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v20, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v18, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_54_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v28, v29)
}
Some(false) => {
let v31 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24bv_5fbitwidth(s, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::Eq, &[v32, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v662 = match if_53_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v34, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v662)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_56_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v663: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v663 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v663) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v664 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v665 = match s.construct(Constructor::eo_bvsmulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v666 = match s.apply(v665, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v667 = match s.apply(v666, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v668 = match s.apply(v664, v667) { Ok(v) => v, Err(e) => return Err(e) };
let v669 = match s.apply(v668, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v669)
}
pub(super) fn more_57_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s: &mut Store, v17: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v663 = match if_55_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v17, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v670 = match requires_56_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v663, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v670))
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
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Eq, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
more_57_eo__24eo_5fprog_5fbv_2dsmulo_2delim(s, v17, v12, v9, v2)
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
pub(super) fn cases_0_20_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_80_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_81_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_82_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_83_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v134: Term, v135: Term) -> CheckResult<Term> {
let v136 = match eo__24iota_5frec(s, v134, v135) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v136)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v122: Term, v123: Term, v12: Term) -> CheckResult<Term> {
if v122 != v123 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v122) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v124 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match eo__24bv_5fbitwidth(s, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_core(EvalOp::Add, &[v128, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_core(EvalOp::Add, &[v126, v130]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_core(EvalOp::Add, &[v131, v132]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.builtin_list(EvalOp::ListRepeat, &[v124, v125, v133]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v134, v135)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v12: Term, v9: Term, v29: Term, v113: Term, v137: Term, v139: Term, v19: Term) -> CheckResult<Term> {
let v140 = match eo__24bv_5fumulo_5felim_5frec(s, v12, v9, v29, v113, v137, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v19, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v141, v142) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v143)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v12: Term, v114: Term, v9: Term, v29: Term, v113: Term, v19: Term) -> CheckResult<Term> {
let v115 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match eo__24bv_5fbitwidth(s, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.builtin_core(EvalOp::Add, &[v116, v117]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.builtin_core(EvalOp::Add, &[v114, v118]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.builtin_core(EvalOp::Add, &[v119, v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_core(EvalOp::IsNeg, &[v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match requires_1_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v122, v123, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match eo__24bv_5fbitwidth(s, v138) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v12, v9, v29, v113, v137, v139, v19)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v102: Term, v100: Term, v97: Term, v96: Term, v86: Term, v76: Term, v71: Term, v70: Term, v12: Term, v9: Term, v29: Term, v19: Term) -> CheckResult<Term> {
let v103 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v102, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v100, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24eo_5ftypeof(s, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match eo__24eo_5fnil(s, v97, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v96, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v86, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v76, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24eo_5ftypeof(s, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24eo_5fnil(s, v71, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v70, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v12, v114, v9, v29, v113, v19)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v9: Term, v90: Term, v87: Term, v12: Term, v86: Term, v76: Term, v71: Term, v70: Term, v29: Term, v19: Term) -> CheckResult<Term> {
let v91 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v92, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v90, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v87, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v98, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v102, v100, v97, v96, v86, v76, v71, v70, v12, v9, v29, v19)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v78: Term, v12: Term, v77: Term, v9: Term, v76: Term, v71: Term, v70: Term, v29: Term, v19: Term) -> CheckResult<Term> {
let v79 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v78, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v82, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v80, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v77, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v88, v89) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v9, v90, v87, v12, v86, v76, v71, v70, v29, v19)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v55: Term, v66: Term, v45: Term, v35: Term, v30: Term, v12: Term, v9: Term, v29: Term, v19: Term) -> CheckResult<Term> {
let v67 = match s.apply(v55, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v45, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v35, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v30, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24bv_5fbitwidth(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match eo__24bv_5fbitwidth(s, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_extract, &[v73, v75]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v78, v12, v77, v9, v76, v71, v70, v29, v19)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v46: Term, v54: Term, v12: Term, v45: Term, v35: Term, v30: Term, v9: Term, v29: Term, v19: Term) -> CheckResult<Term> {
let v55 = match s.apply(v46, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v61, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v59, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24eo_5ftypeof(s, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24eo_5fnil(s, v56, v65) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v55, v66, v45, v35, v30, v12, v9, v29, v19)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v41: Term, v42: Term, v39: Term, v36: Term, v9: Term, v12: Term, v35: Term, v30: Term, v29: Term, v19: Term) -> CheckResult<Term> {
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v39, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v36, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v51, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v49, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v46, v54, v12, v45, v35, v30, v9, v29, v19)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v12: Term, v9: Term, v30: Term, v29: Term, v19: Term) -> CheckResult<Term> {
let v31 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24bv_5fbitwidth(s, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24bv_5fbitwidth(s, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_extract, &[v32, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v37, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v41, v42, v39, v36, v9, v12, v35, v30, v29, v19)
}
pub(super) fn if_11_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, condition: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24bv_5fbitwidth(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Add, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24bv_5fbitwidth(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Add, &[v25, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_extract, &[v23, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v12, v9, v30, v29, v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_12_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v144: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v144 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v144) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v145 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_bvumulo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v146, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v147, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v145, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v150)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dumulo_2delim(s: &mut Store, v17: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v144 = match if_11_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v17, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match requires_12_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v144, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v151))
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
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Eq, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dumulo_2delim(s, v17, v12, v9, v2)
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
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24bv_5fbitwidth(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Pow, &[v15, v17]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
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
let v19 = match if_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24bv_5fbitwidth(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24bv_5fbitwidth(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_core(EvalOp::Pow, &[v34, v36]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v37)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v30 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24bv_5fbitwidth(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::IsNeg, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match if_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
Some(false) => {
let v39 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24bv_5fbitwidth(s, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, v45: Term, v46: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v45 != v46 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v45) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v47 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v49)
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
match s.cached_program(ProgramId(958), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24poly_5fmod_5fcoeffs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(958), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Eq, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24poly_5fmod_5fcoeffs(s, v17, v2, a1, v12, v9)
}
pub(super) fn if_0_eo__24poly_5fmod_5fcoeffs(s: &mut Store, condition: Term, v2: Term, a1: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match eo__24poly_5fmod_5fcoeffs(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::IntMod, &[v22, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::ToRat, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v19, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24poly_5fmod_5fcoeffs(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24poly_5fmod_5fcoeffs(s: &mut Store, v17: Term, v2: Term, a1: Term, v12: Term, v9: Term) -> CheckResult<Option<Term>> {
let v29 = match if_0_eo__24poly_5fmod_5fcoeffs(s, v17, v2, a1, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s: &mut Store, v27: Term, v5: Term, v26: Term, v25: Term, v2: Term) -> CheckResult<Option<Term>> {
let v28 = match eo__24bv_5fbitwidth(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::IsZ, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match if_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v29, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24poly_5fmod_5fcoeffs(s, v26, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_core(EvalOp::Eq, &[v25, v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match requires_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v45, v46, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v50))
}
pub(super) fn if_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToRat, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v5, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.builtin_core(EvalOp::ToInt, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::IsEq, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match Rational::from_integers(&Integer::from(1u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v24 = match s.literal(Lit::Rational(v23)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_4_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::IsBin, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match if_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn cases_0_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$get_bv_poly_norm_rec"
pub fn eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(892), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(892), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
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
pub(super) fn cases_0_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24get_5fbv_5fpoly_5fnorm_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
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
let v24 = match if_1_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24poly_5fmod_5fcoeffs(s, v7, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24get_5fbv_5fpoly_5fnorm_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_5fpoly_5fnorm(s, v27, v5, v26, v25, v2)
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
pub(super) fn cases_0_21_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_84_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_85_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_86_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_87_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v80: Term, v81: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v80 != v81 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v80) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v82, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v86, v89) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v90)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v76: Term, v77: Term, v56: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v76 != v77 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v76) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v78 = match s.builtin_core(EvalOp::ToInt, &[v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.builtin_core(EvalOp::IntMod, &[v78, v79]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match requires_0_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v80, v81, v12, v9, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v91)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v72: Term, v73: Term, v35: Term, v56: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v72 != v73 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v72) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v74 = match s.builtin_core(EvalOp::ToInt, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.builtin_core(EvalOp::IntMod, &[v74, v75]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match requires_1_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v76, v77, v56, v12, v9, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v92)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v72: Term, v73: Term, v35: Term, v56: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Option<Term>> {
let v93 = match requires_2_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v72, v73, v35, v56, v12, v9, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v93))
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v59: Term, v19: Term, v16: Term, v60: Term, v39: Term, v35: Term, v56: Term, v12: Term, v9: Term) -> CheckResult<Option<Term>> {
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
let v73 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v72, v73, v35, v56, v12, v9, v19, v16)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, v41: Term, v43: Term, v42: Term, v12: Term, v9: Term, v25: Term, v19: Term, v16: Term, v39: Term, v35: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v59, v19, v16, v60, v39, v35, v56, v12, v9)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s: &mut Store, a1: Term, v12: Term, v9: Term, v19: Term, v16: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, v41, v43, v42, v12, v9, v25, v19, v16, v39, v35)
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
more_3_eo__24eo_5fprog_5fbv_5fpoly_5fnorm_5feq(s, a1, v12, v9, v19, v16)
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
pub(super) fn more_1_eo__24eo_5fprog_5fstring_5flength_5fpos(s: &mut Store, v21: Term, v23: Term, v20: Term, v19: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v20, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v19, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5flength_5fpos(s: &mut Store, a0: Term, v11: Term, v9: Term, v8: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24seq_5fempty(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v9, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v8, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstring_5flength_5fpos(s, v21, v23, v20, v19)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5flength_5fpos(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5flength_5fpos(s, a0, v11, v9, v8, v0)
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
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v15, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
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
let v6 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24str_5fis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24str_5fis_5fempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match requires_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty(s, v13, v14, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
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
match s.cached_program(ProgramId(1090), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fstrip_5fprefix(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1090), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn more_10_eo__24eo_5fprog_5fconcat_5feq(s: &mut Store, v48: Term, v83: Term, v47: Term) -> CheckResult<Option<Term>> {
let v84 = match s.builtin_list(EvalOp::ListSingletonElim, &[v48, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v47, v84) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v85))
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
more_10_eo__24eo_5fprog_5fconcat_5feq(s, v48, v83, v47)
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
pub(super) fn cases_0_22_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_88_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_89_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_90_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_91_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
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
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v38, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_list(EvalOp::ListRev, &[v37, v39]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
Some(false) => {
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v41, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_2_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, v45: Term, v24: Term, v20: Term) -> CheckResult<Term> {
if v45 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v45) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v48)
}
pub(super) fn requires_3_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, v35: Term, v20: Term, a0: Term, v4: Term, v24: Term) -> CheckResult<Term> {
if v35 != v20 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v35) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match if_1_eo__24eo_5fprog_5fconcat_5funify(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_list(EvalOp::ListNth, &[v36, v43, v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match requires_2_eo__24eo_5fprog_5fconcat_5funify(s, v45, v24, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v49)
}
pub(super) fn more_4_eo__24eo_5fprog_5fconcat_5funify(s: &mut Store, v19: Term, v21: Term, v13: Term, a0: Term, v7: Term, v20: Term, v4: Term) -> CheckResult<Option<Term>> {
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match if_0_eo__24eo_5fprog_5fconcat_5funify(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_list(EvalOp::ListNth, &[v26, v33, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match requires_3_eo__24eo_5fprog_5fconcat_5funify(s, v35, v20, a0, v4, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v50))
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
more_4_eo__24eo_5fprog_5fconcat_5funify(s, v19, v21, v13, a0, v7, v20, v4)
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
pub(super) fn more_5_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5funify(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
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
more_5_eo__24eo_5fcmd_5fstep_5fproven(s, v14, v2, v13)
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v29, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_list(EvalOp::ListRev, &[v28, v30]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
Some(false) => {
let v32 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v32, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
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
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v100 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v101, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.builtin_list(EvalOp::ListRev, &[v100, v102]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v103)
}
Some(false) => {
let v104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v104, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v105)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v127 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v128, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_list(EvalOp::ListRev, &[v127, v129]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v130)
}
Some(false) => {
let v131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v131, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v132)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_6_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v126: Term, v133: Term, v125: Term, v124: Term, v109: Term) -> CheckResult<Term> {
let v134 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_list(EvalOp::ListNth, &[v126, v133, v134]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24eo_5ftypeof(s, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match eo__24eo_5fnil(s, v125, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v124, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v109, v138) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v139)
}
pub(super) fn more_5_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v24: Term, v115: Term, v111: Term, v110: Term, a0: Term, v4: Term, v109: Term) -> CheckResult<Term> {
let v116 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v116, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v119, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v115, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v111, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v110, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match if_4_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fconcat_5fcsplit(s, v126, v133, v125, v124, v109)
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v70 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v71, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.builtin_list(EvalOp::ListRev, &[v70, v72]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v73)
}
Some(false) => {
let v74 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v74, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v75)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_9_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v80: Term, v94: Term, v79: Term, v67: Term) -> CheckResult<Term> {
let v95 = match eo__24eo_5fnil(s, v80, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v79, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v67, v96) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v97)
}
pub(super) fn more_8_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v82: Term, v24: Term, v81: Term, v80: Term, v79: Term, v67: Term) -> CheckResult<Term> {
let v83 = match s.apply(v82, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v83, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v86, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v89, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v85, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v81, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match eo__24eo_5ftypeof(s, v93) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fconcat_5fcsplit(s, v80, v94, v79, v67)
}
pub(super) fn more_7_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v58: Term, v64: Term, v54: Term, v53: Term, a0: Term, v4: Term, v24: Term) -> CheckResult<Term> {
let v65 = match s.apply(v58, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v54, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v53, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match if_2_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_list(EvalOp::ListNth, &[v69, v76, v77]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v68, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fconcat_5fcsplit(s, v82, v24, v81, v80, v79, v67)
}
pub(super) fn if_10_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, condition: Term, v24: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v56, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fconcat_5fcsplit(s, v58, v64, v54, v53, a0, v4, v24)
}
Some(false) => {
let v98 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match if_3_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_list(EvalOp::ListNth, &[v99, v106, v107]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v98, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v112, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fconcat_5fcsplit(s, v24, v115, v111, v110, a0, v4, v109)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_11_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v49: Term, v50: Term, v24: Term, a0: Term, v4: Term) -> CheckResult<Term> {
if v49 != v50 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v49) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v51 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match if_10_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v24, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v52, v140) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v141)
}
pub(super) fn requires_12_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v36: Term, v24: Term, a0: Term, v4: Term) -> CheckResult<Term> {
if v36 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v36) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_1_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_list(EvalOp::ListNth, &[v37, v44, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Length, &[v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::IsEq, &[v47, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match requires_11_eo__24eo_5fprog_5fconcat_5fcsplit(s, v49, v50, v24, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v142)
}
pub(super) fn more_13_eo__24eo_5fprog_5fconcat_5fcsplit(s: &mut Store, v19: Term, v21: Term, v20: Term, v17: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Option<Term>> {
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v26 { return Ok(None); }
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match if_0_eo__24eo_5fprog_5fconcat_5fcsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_list(EvalOp::ListNth, &[v27, v34, v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match requires_12_eo__24eo_5fprog_5fconcat_5fcsplit(s, v36, v24, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v143))
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
more_13_eo__24eo_5fprog_5fconcat_5fcsplit(s, v19, v21, v20, v17, a0, v7, v4)
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
pub(super) fn more_6_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5fcsplit(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
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
more_6_eo__24eo_5fcmd_5fstep_5fproven(s, v14, v2, v13)
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
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v42, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_list(EvalOp::ListRev, &[v41, v43]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
Some(false) => {
let v45 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v45, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v46)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v54 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v55, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_list(EvalOp::ListRev, &[v54, v56]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
Some(false) => {
let v58 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v58, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v59)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
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
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v78, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.builtin_list(EvalOp::ListRev, &[v77, v79]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v80)
}
Some(false) => {
let v81 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v81, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v82)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v132, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.builtin_list(EvalOp::ListRev, &[v131, v133]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v134)
}
Some(false) => {
let v135 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v135, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v136)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v144 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v145, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_list(EvalOp::ListRev, &[v144, v146]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v147)
}
Some(false) => {
let v148 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v148, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v149)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v154 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v155, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.builtin_list(EvalOp::ListRev, &[v154, v156]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v157)
}
Some(false) => {
let v158 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v158, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v159)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v168 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v169, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.builtin_list(EvalOp::ListRev, &[v168, v170]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v171)
}
Some(false) => {
let v172 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v172, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v173)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_13_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v176: Term, v166: Term, v165: Term, v140: Term) -> CheckResult<Term> {
let v177 = match eo__24eo_5ftypeof(s, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match eo__24eo_5fnil(s, v166, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v165, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v140, v179) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v180)
}
pub(super) fn more_2_eo__24str_5funify_5fsplit(s: &mut Store, v22: Term, v34: Term) -> CheckResult<Option<Term>> {
let v35 = match s.apply(v22, v34) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v35))
}
pub(super) fn more_1_eo__24str_5funify_5fsplit(s: &mut Store, a1: Term, a0: Term, v22: Term) -> CheckResult<Option<Term>> {
let v23 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v26, v33) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24str_5funify_5fsplit(s, v22, v34)
}
pub(super) fn more_0_eo__24str_5funify_5fsplit(s: &mut Store, v10: Term, a0: Term, a1: Term, v9: Term) -> CheckResult<Option<Term>> {
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v13, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v9, v21) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5funify_5fsplit(s, a1, a0, v22)
}
pub(super) fn case_0_eo__24str_5funify_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_0_eo__24str_5funify_5fsplit(s, v10, a0, a1, v9)
}
pub(super) fn more_5_eo__24str_5funify_5fsplit(s: &mut Store, v32: Term, v34: Term, v28: Term, v23: Term) -> CheckResult<Option<Term>> {
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v23, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn more_4_eo__24str_5funify_5fsplit(s: &mut Store, v9: Term, v22: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24str_5funify_5fsplit(s, v32, v34, v28, v23)
}
pub(super) fn more_3_eo__24str_5funify_5fsplit(s: &mut Store, v10: Term, a0: Term, a1: Term, v9: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24str_5funify_5fsplit(s, v9, v22, a1, a0)
}
pub(super) fn case_1_eo__24str_5funify_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_3_eo__24str_5funify_5fsplit(s, v10, a0, a1, v9)
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
pub(super) fn more_12_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, a0: Term, v4: Term, v152: Term, v142: Term, v141: Term, v140: Term) -> CheckResult<Term> {
let v153 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match if_10_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListNth, &[v153, v160, v161]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match eo__24str_5funify_5fsplit(s, v152, v162, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v142, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v141, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match if_11_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.builtin_list(EvalOp::ListNth, &[v167, v174, v175]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fconcat_5fsplit(s, v176, v166, v165, v140)
}
pub(super) fn if_5_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
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
pub(super) fn if_6_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v105, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.builtin_list(EvalOp::ListRev, &[v104, v106]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v107)
}
Some(false) => {
let v108 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v108, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v109)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v114 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v115, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.builtin_list(EvalOp::ListRev, &[v114, v116]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v117)
}
Some(false) => {
let v118 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v118, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v119)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_15_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v103: Term, v110: Term, v111: Term, a0: Term, v4: Term, v102: Term, v101: Term, v100: Term, v88: Term) -> CheckResult<Term> {
let v112 = match s.builtin_list(EvalOp::ListNth, &[v103, v110, v111]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match if_7_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_list(EvalOp::ListNth, &[v113, v120, v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match eo__24str_5funify_5fsplit(s, v112, v122, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v102, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match eo__24eo_5ftypeof(s, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24eo_5fnil(s, v101, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v100, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v88, v127) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v128)
}
pub(super) fn more_14_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v64: Term, v87: Term, a0: Term, v4: Term, v7: Term) -> CheckResult<Term> {
let v88 = match s.apply(v64, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match if_5_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.builtin_list(EvalOp::ListNth, &[v90, v97, v98]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v89, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match if_6_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fconcat_5fsplit(s, v103, v110, v111, a0, v4, v102, v101, v100, v88)
}
pub(super) fn if_16_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v64 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match if_3_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_list(EvalOp::ListNth, &[v66, v73, v74]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match if_4_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.builtin_list(EvalOp::ListNth, &[v76, v83, v84]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match eo__24str_5funify_5fsplit(s, v75, v85, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v65, v86) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fconcat_5fsplit(s, v64, v87, a0, v4, v7)
}
Some(false) => {
let v129 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match if_8_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListNth, &[v130, v137, v138]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v129, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match if_9_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.builtin_list(EvalOp::ListNth, &[v143, v150, v151]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4, v152, v142, v141, v140)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v187 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v188, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.builtin_list(EvalOp::ListRev, &[v187, v189]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v190)
}
Some(false) => {
let v191 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v191, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v192)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v200 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v201, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.builtin_list(EvalOp::ListRev, &[v200, v202]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v203)
}
Some(false) => {
let v204 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v204, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v205)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v210 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v211, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_list(EvalOp::ListRev, &[v210, v212]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v213)
}
Some(false) => {
let v214 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v214, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v215)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_23_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v264 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v265, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.builtin_list(EvalOp::ListRev, &[v264, v266]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v267)
}
Some(false) => {
let v268 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v268, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v269)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_24_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v277 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v278, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.builtin_list(EvalOp::ListRev, &[v277, v279]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v280)
}
Some(false) => {
let v281 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v281, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v282)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_25_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v287 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v288, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.builtin_list(EvalOp::ListRev, &[v287, v289]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v290)
}
Some(false) => {
let v291 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v291, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v292)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_26_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v301 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v302, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.builtin_list(EvalOp::ListRev, &[v301, v303]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v304)
}
Some(false) => {
let v305 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v305, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v306)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_28_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v309: Term, v299: Term, v298: Term, v273: Term) -> CheckResult<Term> {
let v310 = match eo__24eo_5ftypeof(s, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match eo__24eo_5fnil(s, v299, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v298, v311) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.apply(v273, v312) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v313)
}
pub(super) fn more_27_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, a0: Term, v4: Term, v285: Term, v275: Term, v274: Term, v7: Term, v273: Term) -> CheckResult<Term> {
let v286 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match if_25_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.builtin_list(EvalOp::ListNth, &[v286, v293, v294]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match eo__24str_5funify_5fsplit(s, v285, v295, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v275, v296) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v274, v297) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match if_26_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.builtin_list(EvalOp::ListNth, &[v300, v307, v308]) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24eo_5fprog_5fconcat_5fsplit(s, v309, v299, v298, v273)
}
pub(super) fn if_20_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v224 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v225, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_list(EvalOp::ListRev, &[v224, v226]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v227)
}
Some(false) => {
let v228 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v228, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v229)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v237 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v238, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.builtin_list(EvalOp::ListRev, &[v237, v239]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v240)
}
Some(false) => {
let v241 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v241, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v242)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_22_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v247 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v248, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.builtin_list(EvalOp::ListRev, &[v247, v249]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v250)
}
Some(false) => {
let v251 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v251, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v252)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_30_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v236: Term, v243: Term, v244: Term, a0: Term, v4: Term, v235: Term, v234: Term, v233: Term, v221: Term) -> CheckResult<Term> {
let v245 = match s.builtin_list(EvalOp::ListNth, &[v236, v243, v244]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match if_22_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.builtin_list(EvalOp::ListNth, &[v246, v253, v254]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match eo__24str_5funify_5fsplit(s, v245, v255, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v235, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match eo__24eo_5ftypeof(s, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match eo__24eo_5fnil(s, v234, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v233, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v221, v260) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v261)
}
pub(super) fn more_29_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v197: Term, v220: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let v221 = match s.apply(v197, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match if_20_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.builtin_list(EvalOp::ListNth, &[v223, v230, v231]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v222, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match if_21_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24eo_5fprog_5fconcat_5fsplit(s, v236, v243, v244, a0, v4, v235, v234, v233, v221)
}
pub(super) fn if_31_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v197 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match if_18_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.builtin_list(EvalOp::ListNth, &[v199, v206, v207]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match if_19_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.builtin_list(EvalOp::ListNth, &[v209, v216, v217]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match eo__24str_5funify_5fsplit(s, v208, v218, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v198, v219) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24eo_5fprog_5fconcat_5fsplit(s, v197, v220, a0, v7, v4)
}
Some(false) => {
let v262 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match if_23_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.builtin_list(EvalOp::ListNth, &[v263, v270, v271]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v262, v272) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match if_24_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.builtin_list(EvalOp::ListNth, &[v276, v283, v284]) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4, v285, v275, v274, v7, v273)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_32_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v326 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v327, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.builtin_list(EvalOp::ListRev, &[v326, v328]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v329)
}
Some(false) => {
let v330 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v330, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v331)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_33_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v336 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v337, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.builtin_list(EvalOp::ListRev, &[v336, v338]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v339)
}
Some(false) => {
let v340 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v340, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v341)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_34_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v350 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v351, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.builtin_list(EvalOp::ListRev, &[v350, v352]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v353)
}
Some(false) => {
let v354 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v354, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v355)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_35_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v360 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v361, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.builtin_list(EvalOp::ListRev, &[v360, v362]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v363)
}
Some(false) => {
let v364 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v364, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v365)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_36_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v381 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v382, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.builtin_list(EvalOp::ListRev, &[v381, v383]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v384)
}
Some(false) => {
let v385 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v385, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v386)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_37_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v391 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v392, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.builtin_list(EvalOp::ListRev, &[v391, v393]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v394)
}
Some(false) => {
let v395 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v395, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v396)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_43_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v403: Term, v376: Term, v375: Term, v320: Term) -> CheckResult<Term> {
let v404 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.apply(v403, v404) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.apply(v376, v405) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.apply(v406, v407) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.apply(v375, v408) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.apply(v320, v409) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v410)
}
pub(super) fn more_42_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, a0: Term, v7: Term, v4: Term, v379: Term, v378: Term, v377: Term, v376: Term, v375: Term, v320: Term) -> CheckResult<Term> {
let v380 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match if_36_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.builtin_list(EvalOp::ListNth, &[v380, v387, v388]) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match if_37_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.builtin_list(EvalOp::ListNth, &[v390, v397, v398]) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match eo__24str_5funify_5fsplit(s, v389, v399, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.apply(v379, v400) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.apply(v378, v401) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.apply(v377, v402) { Ok(v) => v, Err(e) => return Err(e) };
more_43_eo__24eo_5fprog_5fconcat_5fsplit(s, v403, v376, v375, v320)
}
pub(super) fn more_41_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v359: Term, v366: Term, v367: Term, v358: Term, a0: Term, v348: Term, v347: Term, v322: Term, v321: Term, v7: Term, v4: Term, v320: Term) -> CheckResult<Term> {
let v368 = match s.builtin_list(EvalOp::ListNth, &[v359, v366, v367]) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match eo__24str_5funify_5fsplit(s, v358, v368, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.apply(v348, v369) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match eo__24eo_5ftypeof(s, v370) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match eo__24seq_5fempty(s, v371) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v347, v372) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v322, v373) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.apply(v321, v374) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_42_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7, v4, v379, v378, v377, v376, v375, v320)
}
pub(super) fn more_40_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v335: Term, v342: Term, v343: Term, v334: Term, a0: Term, v324: Term, v323: Term, v7: Term, v4: Term, v322: Term, v321: Term, v320: Term) -> CheckResult<Term> {
let v344 = match s.builtin_list(EvalOp::ListNth, &[v335, v342, v343]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match eo__24str_5funify_5fsplit(s, v334, v344, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.apply(v324, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v323, v346) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match if_34_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.builtin_list(EvalOp::ListNth, &[v349, v356, v357]) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match if_35_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_41_eo__24eo_5fprog_5fconcat_5fsplit(s, v359, v366, v367, v358, a0, v348, v347, v322, v321, v7, v4, v320)
}
pub(super) fn more_39_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v50: Term, v319: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let v320 = match s.apply(v50, v319) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match if_32_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.builtin_list(EvalOp::ListNth, &[v325, v332, v333]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match if_33_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_40_eo__24eo_5fprog_5fconcat_5fsplit(s, v335, v342, v343, v334, a0, v324, v323, v7, v4, v322, v321, v320)
}
pub(super) fn more_38_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, a0: Term, v4: Term, v7: Term, v184: Term, v183: Term, v50: Term) -> CheckResult<Term> {
let v185 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match if_17_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.builtin_list(EvalOp::ListNth, &[v186, v193, v194]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v185, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match if_31_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v196, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v184, v315) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v316, v317) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v183, v318) { Ok(v) => v, Err(e) => return Err(e) };
more_39_eo__24eo_5fprog_5fconcat_5fsplit(s, v50, v319, a0, v7, v4)
}
pub(super) fn requires_44_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v49: Term, v28: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
if v49 != v28 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v49) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v50 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match if_2_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.builtin_list(EvalOp::ListNth, &[v53, v60, v61]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v52, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match if_16_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v63, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v51, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_38_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4, v7, v184, v183, v50)
}
pub(super) fn requires_45_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v39: Term, v24: Term, a0: Term, v4: Term, v28: Term, v7: Term) -> CheckResult<Term> {
if v39 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v39) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v40 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match if_1_eo__24eo_5fprog_5fconcat_5fsplit(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_list(EvalOp::ListNth, &[v40, v47, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match requires_44_eo__24eo_5fprog_5fconcat_5fsplit(s, v49, v28, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v411)
}
pub(super) fn more_46_eo__24eo_5fprog_5fconcat_5fsplit(s: &mut Store, v19: Term, v21: Term, v20: Term, v17: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Option<Term>> {
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
let v38 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_list(EvalOp::ListNth, &[v30, v37, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match requires_45_eo__24eo_5fprog_5fconcat_5fsplit(s, v39, v24, a0, v4, v28, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v412))
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
more_46_eo__24eo_5fprog_5fconcat_5fsplit(s, v19, v21, v20, v17, a0, v7, v4)
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
pub(super) fn more_7_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5fsplit(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
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
more_7_eo__24eo_5fcmd_5fstep_5fproven(s, v14, v2, v13)
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
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v38, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_list(EvalOp::ListRev, &[v37, v39]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
Some(false) => {
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v41, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v49 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v50, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_list(EvalOp::ListRev, &[v49, v51]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v52)
}
Some(false) => {
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v53, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v54)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v62 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v63, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.builtin_list(EvalOp::ListRev, &[v62, v64]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v65)
}
Some(false) => {
let v66 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v66, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v67)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v72 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v73, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_list(EvalOp::ListRev, &[v72, v74]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v75)
}
Some(false) => {
let v76 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v76, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v77)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v126 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v127, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.builtin_list(EvalOp::ListRev, &[v126, v128]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v129)
}
Some(false) => {
let v130 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v130, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v131)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v139 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v140, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.builtin_list(EvalOp::ListRev, &[v139, v141]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v142)
}
Some(false) => {
let v143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v143, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v144)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v149 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v150, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.builtin_list(EvalOp::ListRev, &[v149, v151]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v152)
}
Some(false) => {
let v153 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v153, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v154)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v163 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v164, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.builtin_list(EvalOp::ListRev, &[v163, v165]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v166)
}
Some(false) => {
let v167 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v167, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v168)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_13_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v171: Term, v161: Term, v160: Term, v135: Term) -> CheckResult<Term> {
let v172 = match eo__24eo_5ftypeof(s, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match eo__24eo_5fnil(s, v161, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v160, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v135, v174) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v175)
}
pub(super) fn more_12_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, a0: Term, v4: Term, v147: Term, v137: Term, v136: Term, v135: Term) -> CheckResult<Term> {
let v148 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match if_10_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.builtin_list(EvalOp::ListNth, &[v148, v155, v156]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match eo__24str_5funify_5fsplit(s, v147, v157, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v137, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v136, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match if_11_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.builtin_list(EvalOp::ListNth, &[v162, v169, v170]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fconcat_5flprop(s, v171, v161, v160, v135)
}
pub(super) fn if_5_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v86 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v87, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_list(EvalOp::ListRev, &[v86, v88]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v89)
}
Some(false) => {
let v90 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v90, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v91)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v99 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v100, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_list(EvalOp::ListRev, &[v99, v101]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v102)
}
Some(false) => {
let v103 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v103, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v104)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
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
pub(super) fn more_15_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v98: Term, v105: Term, v106: Term, a0: Term, v4: Term, v97: Term, v96: Term, v95: Term, v83: Term) -> CheckResult<Term> {
let v107 = match s.builtin_list(EvalOp::ListNth, &[v98, v105, v106]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match if_7_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.builtin_list(EvalOp::ListNth, &[v108, v115, v116]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match eo__24str_5funify_5fsplit(s, v107, v117, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v97, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match eo__24eo_5ftypeof(s, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match eo__24eo_5fnil(s, v96, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v95, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v83, v122) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v123)
}
pub(super) fn more_14_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v59: Term, v82: Term, a0: Term, v4: Term, v7: Term) -> CheckResult<Term> {
let v83 = match s.apply(v59, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match if_5_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.builtin_list(EvalOp::ListNth, &[v85, v92, v93]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v84, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match if_6_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fconcat_5flprop(s, v98, v105, v106, a0, v4, v97, v96, v95, v83)
}
pub(super) fn if_16_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v59 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match if_3_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_list(EvalOp::ListNth, &[v61, v68, v69]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match if_4_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.builtin_list(EvalOp::ListNth, &[v71, v78, v79]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match eo__24str_5funify_5fsplit(s, v70, v80, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v60, v81) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fconcat_5flprop(s, v59, v82, a0, v4, v7)
}
Some(false) => {
let v124 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match if_8_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.builtin_list(EvalOp::ListNth, &[v125, v132, v133]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v124, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match if_9_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_list(EvalOp::ListNth, &[v138, v145, v146]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4, v147, v137, v136, v135)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v184 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v185, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.builtin_list(EvalOp::ListRev, &[v184, v186]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v187)
}
Some(false) => {
let v188 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v188, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v189)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v194 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v195, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_list(EvalOp::ListRev, &[v194, v196]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v197)
}
Some(false) => {
let v198 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v198, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v199)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v208 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v209, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.builtin_list(EvalOp::ListRev, &[v208, v210]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v211)
}
Some(false) => {
let v212 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v212, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v213)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_20_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v218 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v219, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.builtin_list(EvalOp::ListRev, &[v218, v220]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v221)
}
Some(false) => {
let v222 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v222, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v223)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
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
pub(super) fn if_22_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v249 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v250, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.builtin_list(EvalOp::ListRev, &[v249, v251]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v252)
}
Some(false) => {
let v253 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v253, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v254)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_27_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v264: Term, v233: Term, v178: Term) -> CheckResult<Term> {
let v265 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v264, v265) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v233, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v178, v267) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v268)
}
pub(super) fn more_26_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v238: Term, v245: Term, v246: Term, a0: Term, v4: Term, v237: Term, v236: Term, v235: Term, v234: Term, v233: Term, v178: Term) -> CheckResult<Term> {
let v247 = match s.builtin_list(EvalOp::ListNth, &[v238, v245, v246]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match if_22_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.builtin_list(EvalOp::ListNth, &[v248, v255, v256]) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match eo__24str_5funify_5fsplit(s, v247, v257, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v237, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v236, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v235, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v261, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v234, v263) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24eo_5fprog_5fconcat_5flprop(s, v264, v233, v178)
}
