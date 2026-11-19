//! Generated functions, module 7 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn case_296_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsle_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dsle_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate(s: &mut Store, v14: Term, a0: Term, v13: Term, a1: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a1 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvredor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate(s, v14, a0, v13, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dredor_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-redor-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dredor_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dredor_2deliminate(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_297_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fredor_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fprog_5fbv_2dredor_2deliminate(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate(s: &mut Store, v14: Term, a0: Term, v13: Term, a1: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v18, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a1 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvredand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate(s, v14, a0, v13, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dredand_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-redand-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dredand_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dredand_2deliminate(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_298_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fredand_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fprog_5fbv_2dredand_2deliminate(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dule_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dule_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dule_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ule-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dule_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dule_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_299_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fule_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dule_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_74_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_296_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_297_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_298_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_299_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s: &mut Store, v12: Term, v9: Term, v4: Term) -> CheckResult<Option<Term>> {
let v13 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(v17)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v4, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s, v12, v9, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-comp-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_300_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fcomp_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v142: Term, v144: Term, v141: Term, v135: Term) -> CheckResult<Option<Term>> {
let v145 = match s.apply(v142, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Binary(BitVec::new(0, &v146))) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v145, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v141, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v135, v149) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v150))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, a1: Term, a0: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v132 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_rotate_5fleft, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v133, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v132, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Numeral(v137)) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_extract, &[a2, v138]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v139, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v136, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_extract, &[a3, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v142, v144, v141, v135)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v118: Term, v119: Term, a0: Term, v112: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v120 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v118 != v120 { return Ok(None); }
if v119 != a0 { return Ok(None); }
let v121 = match s.unapply(v112) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v122, v123)) = v121 else { return Ok(None); }
;
let v124 = match s.unapply(v122) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v125, v126)) = v124 else { return Ok(None); }
;
let v127 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v125 != v127 { return Ok(None); }
if v126 != a1 { return Ok(None); }
let v128 = match s.unapply(v123) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v129, v130)) = v128 else { return Ok(None); }
;
let v131 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v129 != v131 { return Ok(None); }
if v130 != a0 { return Ok(None); }
more_7_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, a1, a0, a2, a3, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v90: Term, v100: Term, a8: Term, a4: Term, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if v90 != v100 { return Ok(None); }
let v101 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v101 else { return Ok(None); }
;
let v102 = fields[0];
let v103 = match s.unapply(v102) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v104, v105)) = v103 else { return Ok(None); }
;
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v107 != v109 { return Ok(None); }
if v108 != a4 { return Ok(None); }
let v110 = match s.unapply(v105) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.unapply(v111) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v114 != v116 { return Ok(None); }
let v117 = match s.unapply(v115) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v118, v119)) = v117 else { return Ok(None); }
;
more_6_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v118, v119, a0, v112, a1, a2, a3, a4)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v85: Term, v86: Term, a3: Term, v83: Term, a0: Term, a8: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v87 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v85 != v87 { return Ok(None); }
if v86 != a3 { return Ok(None); }
let v88 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v92, v93)) = v91 else { return Ok(None); }
;
let v94 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v92 != v94 { return Ok(None); }
let v95 = match s.unapply(v93) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v96 != v98 { return Ok(None); }
if v97 != a0 { return Ok(None); }
let v99 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(v99)) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v90, v100, a8, a4, a0, a1, a2, a3)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v70: Term, v71: Term, a1: Term, v68: Term, a0: Term, v61: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
let v72 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
if v71 != a1 { return Ok(None); }
let v73 = match s.unapply(v68) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v74 != v76 { return Ok(None); }
if v75 != a0 { return Ok(None); }
let v77 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Numeral(v77)) { Ok(v) => v, Err(e) => return Err(e) };
if v61 != v78 { return Ok(None); }
let v79 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v79 else { return Ok(None); }
;
let v80 = fields[0];
let v81 = match s.unapply(v80) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v82, v83)) = v81 else { return Ok(None); }
;
let v84 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v85, v86)) = v84 else { return Ok(None); }
;
more_4_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v85, v86, a3, v83, a0, a8, a4, a1, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v41: Term, a1: Term, a0: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
let v50 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
let v57 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v58 { return Ok(None); }
let v59 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
let v62 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v63 != v65 { return Ok(None); }
let v66 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v67, v68)) = v66 else { return Ok(None); }
;
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v70, v71, a1, v68, a0, v61, a7, a3, a8, a4, a2)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v33: Term, a2: Term, v34: Term, a0: Term, a1: Term, a7: Term, a3: Term, a8: Term, a4: Term) -> CheckResult<Option<Term>> {
let v35 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v36 != v38 { return Ok(None); }
if v37 != a2 { return Ok(None); }
let v39 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v40, v41)) = v39 else { return Ok(None); }
;
let v42 = match s.unapply(v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v43 != v45 { return Ok(None); }
let v46 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v47 != v49 { return Ok(None); }
if v48 != a0 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v41, a1, a0, a7, a3, a8, a4, a2)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v20: Term, v22: Term, v21: Term, a1: Term, v18: Term, a0: Term, v11: Term, v4: Term, a6: Term, a2: Term, a7: Term, a3: Term, a8: Term, a4: Term) -> CheckResult<Option<Term>> {
if v20 != v22 { return Ok(None); }
if v21 != a1 { return Ok(None); }
let v23 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a0 { return Ok(None); }
let v27 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(v27)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v28 { return Ok(None); }
let v29 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v29 { return Ok(None); }
let v30 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v30 else { return Ok(None); }
;
let v31 = fields[0];
let v32 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v33, v34)) = v32 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v33, a2, v34, a0, a1, a7, a3, a8, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v20, v22, v21, a1, v18, a0, v11, v4, a6, a2, a7, a3, a8, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-rotate-left-eliminate-1"
pub fn eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8);
s.leave();
result
}
pub(super) fn more_44_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v29 { return Ok(None); }
let v30 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__24eo_5fpf, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24eo_5fpf, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__24eo_5fpf, &[v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v2, v5, v8, v11, v14, v31, v33, v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn case_301_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v20 else { return Ok(None); }
;
let v21 = fields[0];
let v22 = fields[1];
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
more_44_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_rotate_5fleft, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s, v17, v19, v18, a0, v4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-rotate-left-eliminate-2"
pub fn eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_302_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, a3: Term, a4: Term, a0: Term, v111: Term, v110: Term, v104: Term) -> CheckResult<Option<Term>> {
let v112 = match s.construct(Constructor::eo_extract, &[a3, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v112, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v111, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Binary(BitVec::new(0, &v115))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v114, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v110, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v104, v118) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v119))
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v98: Term, v100: Term, v99: Term, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
if v98 != v100 { return Ok(None); }
if v99 != a0 { return Ok(None); }
let v101 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_rotate_5fright, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Numeral(v106)) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_extract, &[a2, v107]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v105, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, a3, a4, a0, v111, v110, v104)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v82: Term, a4: Term, a1: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v83 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v87, v88)) = v86 else { return Ok(None); }
;
let v89 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v87 != v89 { return Ok(None); }
if v88 != a4 { return Ok(None); }
let v90 = match s.unapply(v85) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v94, v95)) = v93 else { return Ok(None); }
;
let v96 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v96 { return Ok(None); }
if v95 != a1 { return Ok(None); }
let v97 = match s.unapply(v92) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v98, v99)) = v97 else { return Ok(None); }
;
let v100 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v98, v100, v99, a0, a1, a2, a3, a4)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v66: Term, a3: Term, v63: Term, a0: Term, a8: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v66 != a3 { return Ok(None); }
let v68 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.unapply(v69) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v72, v73)) = v71 else { return Ok(None); }
;
let v74 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v72 != v74 { return Ok(None); }
let v75 = match s.unapply(v73) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v76, v77)) = v75 else { return Ok(None); }
;
let v78 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v76 != v78 { return Ok(None); }
if v77 != a0 { return Ok(None); }
let v79 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(v79)) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v80 { return Ok(None); }
let v81 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v81 else { return Ok(None); }
;
let v82 = fields[0];
more_4_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v82, a4, a1, a0, a2, a3)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v51: Term, a1: Term, v48: Term, a0: Term, v41: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
if v51 != a1 { return Ok(None); }
let v53 = match s.unapply(v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
if v55 != a0 { return Ok(None); }
let v57 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
if v41 != v58 { return Ok(None); }
let v59 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v59 else { return Ok(None); }
;
let v60 = fields[0];
let v61 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
let v67 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v65 != v67 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v66, a3, v63, a0, a8, a4, a1, a2)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v33: Term, a2: Term, v34: Term, a1: Term, a0: Term, a7: Term, a3: Term, a8: Term, a4: Term) -> CheckResult<Option<Term>> {
let v35 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v36 != v38 { return Ok(None); }
if v37 != a2 { return Ok(None); }
let v39 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v40, v41)) = v39 else { return Ok(None); }
;
let v42 = match s.unapply(v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v43 != v45 { return Ok(None); }
let v46 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v52 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v51, a1, v48, a0, v41, a7, a3, a8, a4, a2)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v20: Term, v22: Term, v21: Term, a1: Term, v18: Term, a0: Term, v11: Term, v4: Term, a6: Term, a2: Term, a7: Term, a3: Term, a8: Term, a4: Term) -> CheckResult<Option<Term>> {
if v20 != v22 { return Ok(None); }
if v21 != a1 { return Ok(None); }
let v23 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a0 { return Ok(None); }
let v27 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(v27)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v28 { return Ok(None); }
let v29 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v29 { return Ok(None); }
let v30 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v30 else { return Ok(None); }
;
let v31 = fields[0];
let v32 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v33, v34)) = v32 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v33, a2, v34, a1, a0, a7, a3, a8, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v20, v22, v21, a1, v18, a0, v11, v4, a6, a2, a7, a3, a8, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-rotate-right-eliminate-1"
pub fn eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8);
s.leave();
result
}
pub(super) fn more_45_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v29 { return Ok(None); }
let v30 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__24eo_5fpf, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24eo_5fpf, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__24eo_5fpf, &[v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v2, v5, v8, v11, v14, v31, v33, v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn case_303_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v20 else { return Ok(None); }
;
let v21 = fields[0];
let v22 = fields[1];
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
more_45_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn cases_0_75_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_300_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_301_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_302_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_303_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_18_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_72_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_73_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_74_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_75_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_rotate_5fright, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s, v17, v19, v18, a0, v4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-rotate-right-eliminate-2"
pub fn eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_304_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate(s: &mut Store, v10: Term, v11: Term, v9: Term, v7: Term, v5: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match eo__24eo_5fnil(s, v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v7, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v5, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvnand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate(s, v10, v11, v9, v7, v5, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dnand_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-nand-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dnand_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dnand_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_305_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fnand_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dnand_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate(s: &mut Store, v10: Term, v11: Term, v9: Term, v7: Term, v5: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match eo__24eo_5fnil(s, v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v7, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v5, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvnor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate(s, v10, v11, v9, v7, v5, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dnor_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-nor-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dnor_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dnor_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_306_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fnor_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dnor_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s: &mut Store, v10: Term, v11: Term, v9: Term, v7: Term, v5: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match eo__24eo_5fnil(s, v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v7, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v5, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvxnor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s, v10, v11, v9, v7, v5, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xnor-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_307_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxnor_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dxnor_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_76_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_304_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_305_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_306_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_307_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a1: Term, v125: Term, v112: Term, v93: Term, v26: Term) -> CheckResult<Option<Term>> {
let v126 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v125, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v112, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v93, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v26, v131) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v132))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v94: Term, v111: Term, a2: Term, a1: Term, v93: Term, v26: Term) -> CheckResult<Option<Term>> {
let v112 = match s.apply(v94, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v114, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.literal(Lit::Numeral(v118)) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v119]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(v121)) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v120, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v117, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v113, v124) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a1, v125, v112, v93, v26)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v97: Term, a0: Term, v96: Term, v95: Term, v94: Term, a2: Term, a1: Term, v93: Term, v26: Term) -> CheckResult<Option<Term>> {
let v98 = match s.apply(v97, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v96, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Numeral(v100)) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v101]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(v103)) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v102, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v99, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v95, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v94, v111, a2, a1, v93, v26)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v74: Term, v85: Term, a1: Term, v73: Term, v54: Term, v53: Term, a2: Term, a0: Term, v26: Term) -> CheckResult<Option<Term>> {
let v86 = match s.apply(v74, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v86, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v73, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v54, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v53, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v97, a0, v96, v95, v94, a2, a1, v93, v26)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v71: Term, a0: Term, v55: Term, a2: Term, a1: Term, v54: Term, v53: Term, v26: Term) -> CheckResult<Option<Term>> {
let v72 = match s.apply(v71, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v55, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(v79)) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Numeral(v82)) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v81, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v78, v84) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v74, v85, a1, v73, v54, v53, a2, a0, v26)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a2: Term, a0: Term, v57: Term, v56: Term, v55: Term, a1: Term, v54: Term, v53: Term, v26: Term) -> CheckResult<Option<Term>> {
let v58 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v57, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(v61)) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v62]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(v64)) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v63, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v60, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v56, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v71, a0, v55, a2, a1, v54, v53, v26)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v41: Term, v43: Term, v40: Term, v27: Term, a2: Term, a0: Term, a1: Term, v26: Term) -> CheckResult<Option<Term>> {
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(v45)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(v48)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v40, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v27, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a2, a0, v57, v56, v55, a1, v54, v53, v26)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a2: Term, a0: Term, v29: Term, v28: Term, a1: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(v33)) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Numeral(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v32, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v28, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v41, v43, v40, v27, a2, a0, a1, v26)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvsdiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a2, a0, v29, v28, a1, v27, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v17, v19, v18, a0, v11, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sdiv-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_46_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_308_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsdiv_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fpf, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_46_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s: &mut Store, v11: Term, v13: Term, v9: Term, v3: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v9, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v3, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v4, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Binary(BitVec::new(0, &v12))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s, v11, v13, v9, v3)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-zero-extend-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_309_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v18: Term, v71: Term, v17: Term) -> CheckResult<Option<Term>> {
let v72 = match s.apply(v18, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(v73)) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v74]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(v76)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v72, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v17, v79) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v80))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v56: Term, v58: Term, v53: Term, a0: Term, v52: Term, v51: Term, v35: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v53, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Binary(BitVec::new(0, &v63))) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v60, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match eo__24eo_5ftypeof(s, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24eo_5fnil(s, v52, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v51, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v35, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v19, v70) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v18, v71, v17)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v37: Term, v43: Term, a1: Term, v36: Term, a0: Term, v35: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v44 = match s.apply(v37, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Binary(BitVec::new(0, &v47))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v44, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v36, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(v54)) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v55]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v56, v58, v53, a0, v52, v51, v35, v19, v18, v17)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, a0: Term, v28: Term, v20: Term, a1: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Binary(BitVec::new(0, &v31))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v28, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v20, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(v38)) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(v41)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v37, v43, a1, v36, a0, v35, v19, v18, v17)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v14: Term, a0: Term, a1: Term, v13: Term, a2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v21, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, a0, v28, v20, a1, v19, v18, v17)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvuaddo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v14, a0, a1, v13, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-uaddo-eliminate"
pub fn eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_47_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_310_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fuaddo_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fpf, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_47_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v117: Term, v137: Term, v116: Term, v85: Term, v84: Term, v26: Term) -> CheckResult<Option<Term>> {
let v138 = match s.apply(v117, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v138, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v116, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v85, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v142, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v84, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v26, v145) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v146))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a0: Term, v123: Term, v121: Term, v119: Term, v118: Term, v117: Term, v116: Term, v85: Term, v84: Term, v26: Term) -> CheckResult<Option<Term>> {
let v124 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24eo_5fnil(s, v124, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v123, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v121, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v119, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v118, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(v131)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v132]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.literal(Lit::Numeral(v134)) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v133, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v130, v136) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v117, v137, v116, v85, v84, v26)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v100: Term, v111: Term, v99: Term, v86: Term, a2: Term, a0: Term, a1: Term, v85: Term, v84: Term, v26: Term) -> CheckResult<Option<Term>> {
let v112 = match s.apply(v100, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v99, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v86, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a0, v123, v121, v119, v118, v117, v116, v85, v84, v26)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v91: Term, v97: Term, v87: Term, a2: Term, a1: Term, v86: Term, a0: Term, v85: Term, v84: Term, v26: Term) -> CheckResult<Option<Term>> {
let v98 = match s.apply(v91, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v87, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.literal(Lit::Numeral(v105)) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v106]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.literal(Lit::Numeral(v108)) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v104, v110) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v100, v111, v99, v86, a2, a0, a1, v85, v84, v26)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v27: Term, v83: Term, a2: Term, a0: Term, a1: Term, v26: Term) -> CheckResult<Option<Term>> {
let v84 = match s.apply(v27, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v88, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Numeral(v92)) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v93]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Numeral(v95)) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v94, v96) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v91, v97, v87, a2, a1, v86, a0, v85, v84, v26)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v63: Term, v69: Term, v61: Term, v60: Term, v59: Term, v58: Term, v27: Term, a2: Term, a0: Term, a1: Term, v26: Term) -> CheckResult<Option<Term>> {
let v70 = match s.apply(v63, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v61, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v60, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(v73)) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v74]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(v76)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v72, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v59, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v58, v82) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v27, v83, a2, a0, a1, v26)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v28: Term, v57: Term, a2: Term, a0: Term, a1: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v58 = match s.apply(v28, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24eo_5fnil(s, v66, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v65, v68) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v63, v69, v61, v60, v59, v58, v27, a2, a0, a1, v26)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a2: Term, a1: Term, v43: Term, v42: Term, v41: Term, v28: Term, a0: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v44 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Numeral(v50)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v46, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v42, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v54, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v41, v56) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v28, v57, a2, a0, a1, v27, v26)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a2: Term, a0: Term, v29: Term, a1: Term, v28: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v33, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v29, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a2, a1, v43, v42, v41, v28, a0, v27, v26)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvsaddo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a2, a0, v29, a1, v28, v27, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v17, v19, v18, a0, v11, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-saddo-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_48_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_311_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsaddo_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fpf, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_48_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn cases_0_77_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_308_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_309_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_310_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_311_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v73: Term, v62: Term, v39: Term) -> CheckResult<Option<Term>> {
let v74 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v62, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v39, v76) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v77))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v42: Term, v60: Term, v40: Term, a1: Term, a2: Term, v39: Term) -> CheckResult<Option<Term>> {
let v61 = match s.apply(v42, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v40, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(v68)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v66, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v65, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v63, v72) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v73, v62, v39)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v45: Term, v43: Term, a3: Term, v42: Term, v40: Term, a1: Term, a2: Term, v39: Term) -> CheckResult<Option<Term>> {
let v46 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v43, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Numeral(v53)) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v52, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v51, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Binary(BitVec::new(0, &v57))) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v50, v59) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v42, v60, v40, a1, a2, v39)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v32: Term, v34: Term, v33: Term, a1: Term, a0: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v32 != v34 { return Ok(None); }
if v33 != a1 { return Ok(None); }
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_bvsdivo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(v44)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v45, v43, a3, v42, v40, a1, a2, v39)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a5: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v30 { return Ok(None); }
if v29 != a2 { return Ok(None); }
let v31 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v32, v34, v33, a1, a0, a3, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a3 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v17, v19, v18, a0, v11, a5, a2, a1, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sdivo-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_49_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_312_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsdivo_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v20 { return Ok(None); }
more_49_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_33_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v461: Term, a1: Term, v460: Term, v446: Term, v427: Term, v426: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v462 = match s.apply(v461, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v463 = match s.apply(v460, v462) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match s.apply(v446, v463) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match s.apply(v427, v464) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.apply(v426, v465) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match s.apply(v311, v466) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match s.apply(v192, v467) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match s.apply(v123, v468) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match s.apply(v39, v469) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v470))
}
pub(super) fn more_32_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v447: Term, v446: Term, v427: Term, v426: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v448 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match s.apply(v449, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match s.apply(v448, v450) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.literal(Lit::Numeral(v452)) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v453]) { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.literal(Lit::Numeral(v455)) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match s.apply(v454, v456) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.apply(v451, v457) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match s.apply(v447, v458) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.apply(v459, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v461 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_33_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v461, a1, v460, v446, v427, v426, v311, v192, v123, v39)
}
pub(super) fn more_31_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v433: Term, v429: Term, a0: Term, v428: Term, a3: Term, a1: Term, v427: Term, v426: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v434 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match s.literal(Lit::Numeral(v434)) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v435]) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.literal(Lit::Numeral(v437)) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match s.apply(v436, v438) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.apply(v433, v439) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.apply(v429, v440) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match s.apply(v441, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v444 = match s.apply(v443, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match s.apply(v442, v444) { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match s.apply(v428, v445) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_32_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v447, v446, v427, v426, v311, v192, v123, v39)
}
pub(super) fn more_30_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v421: Term, v384: Term, v383: Term, v381: Term, v342: Term, a3: Term, a0: Term, a1: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v422 = match eo__24eo_5ftypeof(s, v421) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match eo__24eo_5fnil(s, v384, v422) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match s.apply(v383, v423) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match s.apply(v381, v424) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.apply(v342, v425) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match s.apply(v431, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.apply(v430, v432) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v433, v429, a0, v428, a3, a1, v427, v426, v311, v192, v123, v39)
}
pub(super) fn more_29_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v405: Term, v407: Term, v404: Term, a1: Term, v403: Term, v384: Term, v383: Term, v381: Term, v342: Term, a3: Term, a0: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v408 = match s.apply(v405, v407) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.literal(Lit::Numeral(v409)) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v410]) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.literal(Lit::Numeral(v412)) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.apply(v411, v413) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.apply(v408, v414) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.apply(v404, v415) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.apply(v416, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.apply(v418, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.apply(v417, v419) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.apply(v403, v420) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v421, v384, v383, v381, v342, a3, a0, a1, v311, v192, v123, v39)
}
pub(super) fn more_28_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v393: Term, v395: Term, v390: Term, v386: Term, a0: Term, v385: Term, a3: Term, a1: Term, v384: Term, v383: Term, v381: Term, v342: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v396 = match s.apply(v393, v395) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v390, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.apply(v386, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.apply(v398, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.apply(v400, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.apply(v399, v401) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.apply(v385, v402) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.apply(v406, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v405, v407, v404, a1, v403, v384, v383, v381, v342, a3, a0, v311, v192, v123, v39)
}
pub(super) fn more_27_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a1: Term, a3: Term, a0: Term, v381: Term, v342: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v382 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.apply(v382, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.apply(v388, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.apply(v387, v389) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.literal(Lit::Numeral(v391)) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v392]) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.literal(Lit::Numeral(v394)) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v393, v395, v390, v386, a0, v385, a3, a1, v384, v383, v381, v342, v311, v192, v123, v39)
}
pub(super) fn more_26_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v367: Term, v363: Term, a1: Term, v362: Term, v343: Term, a3: Term, a0: Term, v342: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v368 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.literal(Lit::Numeral(v368)) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v369]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.literal(Lit::Numeral(v371)) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v370, v372) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v367, v373) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.apply(v363, v374) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.apply(v375, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.apply(v377, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.apply(v376, v378) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.apply(v362, v379) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.apply(v343, v380) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a1, a3, a0, v381, v342, v311, v192, v123, v39)
}
pub(super) fn more_25_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v349: Term, v355: Term, v345: Term, a0: Term, v344: Term, a3: Term, a1: Term, v343: Term, v342: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v356 = match s.apply(v349, v355) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.apply(v345, v356) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.apply(v357, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.apply(v359, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.apply(v358, v360) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.apply(v344, v361) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.apply(v365, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.apply(v364, v366) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v367, v363, a1, v362, v343, a3, a0, v342, v311, v192, v123, v39)
}
pub(super) fn more_24_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v312: Term, v341: Term, a3: Term, a0: Term, a1: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v342 = match s.apply(v312, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.apply(v347, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.apply(v346, v348) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.literal(Lit::Numeral(v350)) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v351]) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.literal(Lit::Numeral(v353)) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.apply(v352, v354) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v349, v355, v345, a0, v344, a3, a1, v343, v342, v311, v192, v123, v39)
}
pub(super) fn more_23_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v327: Term, v326: Term, v325: Term, v312: Term, a0: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v328 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.apply(v328, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v327, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.literal(Lit::Numeral(v331)) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v332]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.literal(Lit::Numeral(v334)) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v333, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.apply(v330, v336) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v326, v337) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v338, v339) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v325, v340) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v312, v341, a3, a0, a1, v311, v192, v123, v39)
}
pub(super) fn more_22_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, v313: Term, a1: Term, v312: Term, v311: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v314 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v315, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.apply(v314, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.literal(Lit::Numeral(v318)) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v319]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.literal(Lit::Numeral(v321)) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.apply(v320, v322) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v317, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v313, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v327, v326, v325, v312, a0, v311, v192, v123, v39)
}
pub(super) fn more_21_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a1: Term, v301: Term, v287: Term, v268: Term, v267: Term, v266: Term, v264: Term, v223: Term, a3: Term, a0: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v302 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v302, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v301, v303) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.apply(v287, v304) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v268, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match eo__24eo_5ftypeof(s, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match eo__24eo_5fnil(s, v267, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v266, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v264, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v223, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, v313, a1, v312, v311, v192, v123, v39)
}
pub(super) fn more_20_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v287: Term, v268: Term, v267: Term, v266: Term, v264: Term, v223: Term, a0: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v288 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v290, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.apply(v289, v291) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.literal(Lit::Numeral(v293)) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v294]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.literal(Lit::Numeral(v296)) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v295, v297) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.apply(v292, v298) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v288, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v300, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a1, v301, v287, v268, v267, v266, v264, v223, a3, a0, v192, v123, v39)
}
pub(super) fn more_19_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v271: Term, v273: Term, v270: Term, a0: Term, v269: Term, a3: Term, a1: Term, v268: Term, v267: Term, v266: Term, v264: Term, v223: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v274 = match s.apply(v271, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.literal(Lit::Numeral(v275)) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v276]) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.literal(Lit::Numeral(v278)) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v277, v279) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.apply(v274, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v270, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v282, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.apply(v284, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v283, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v269, v286) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v287, v268, v267, v266, v264, v223, a0, v192, v123, v39)
}
pub(super) fn more_18_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v244: Term, v261: Term, v225: Term, v224: Term, a1: Term, a3: Term, a0: Term, v223: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v262 = match s.apply(v244, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v225, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v224, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v265, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v272, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v271, v273, v270, a0, v269, a3, a1, v268, v267, v266, v264, v223, v192, v123, v39)
}
pub(super) fn more_17_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v247: Term, a1: Term, v246: Term, v245: Term, v244: Term, v225: Term, v224: Term, a3: Term, a0: Term, v223: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v248 = match s.apply(v247, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v246, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.literal(Lit::Numeral(v250)) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v251]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.literal(Lit::Numeral(v253)) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v252, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v249, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v245, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v257, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v259, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v258, v260) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v244, v261, v225, v224, a1, a3, a0, v223, v192, v123, v39)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v234: Term, v231: Term, v227: Term, a0: Term, v226: Term, a3: Term, a1: Term, v225: Term, v224: Term, v223: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v235 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.literal(Lit::Numeral(v235)) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v234, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v231, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v227, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v239, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v241, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v240, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v226, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v247, a1, v246, v245, v244, v225, v224, a3, a0, v223, v192, v123, v39)
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v206: Term, v221: Term, v193: Term, a3: Term, a0: Term, a1: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v222 = match s.apply(v206, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v193, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v229, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v228, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.literal(Lit::Numeral(v232)) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v233]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v234, v231, v227, a0, v226, a3, a1, v225, v224, v223, v192, v123, v39)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v207: Term, v206: Term, v193: Term, a0: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v208 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v209, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v208, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.literal(Lit::Numeral(v212)) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v213]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.literal(Lit::Numeral(v215)) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v214, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v211, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v207, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v219, v220) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v206, v221, v193, a3, a0, a1, v192, v123, v39)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, a1: Term, v193: Term, v192: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v194 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.apply(v196, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v195, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.literal(Lit::Numeral(v199)) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v200]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.literal(Lit::Numeral(v202)) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v201, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v198, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v194, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v207, v206, v193, a0, v192, v123, v39)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v180: Term, v178: Term, v174: Term, a1: Term, v173: Term, v154: Term, a3: Term, a0: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v181 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v180]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.literal(Lit::Numeral(v182)) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v181, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v178, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v174, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v186, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v188, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v187, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v173, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v154, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, a1, v193, v192, v123, v39)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v156: Term, v167: Term, a0: Term, v155: Term, a3: Term, a1: Term, v154: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v168 = match s.apply(v156, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v169, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v155, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v176, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v175, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.literal(Lit::Numeral(v179)) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v180, v178, v174, a1, v173, v154, a3, a0, v123, v39)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v124: Term, v153: Term, a3: Term, a0: Term, a1: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v154 = match s.apply(v124, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v158, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v157, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.literal(Lit::Numeral(v161)) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v162]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.literal(Lit::Numeral(v164)) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v163, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v160, v166) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v156, v167, a0, v155, a3, a1, v154, v123, v39)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v139: Term, v138: Term, v137: Term, v124: Term, a0: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v140 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v140, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v139, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(v143)) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v144]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Numeral(v146)) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v145, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v142, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v138, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v150, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v137, v152) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v124, v153, a3, a0, a1, v123, v39)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, v125: Term, a1: Term, v124: Term, v123: Term, v39: Term) -> CheckResult<Option<Term>> {
let v126 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v127, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v126, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::Numeral(v130)) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.literal(Lit::Numeral(v133)) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v132, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v129, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v125, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v139, v138, v137, v124, a0, v123, v39)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v112: Term, v109: Term, v105: Term, a1: Term, v104: Term, v85: Term, a3: Term, a0: Term, v39: Term) -> CheckResult<Option<Term>> {
let v113 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(v113)) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v112, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v109, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v105, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v119, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v118, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v104, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v85, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, v125, a1, v124, v123, v39)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v99: Term, a0: Term, v86: Term, a3: Term, a1: Term, v85: Term, v39: Term) -> CheckResult<Option<Term>> {
let v100 = match s.apply(v99, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v100, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v86, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v106, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.literal(Lit::Numeral(v110)) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v111]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v112, v109, v105, a1, v104, v85, a3, a0, v39)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, a1: Term, v85: Term, v39: Term) -> CheckResult<Option<Term>> {
let v86 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v88, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Numeral(v92)) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v93]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Numeral(v95)) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v94, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v91, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v87, v98) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v99, a0, v86, a3, a1, v85, v39)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v61: Term, v72: Term, a1: Term, v60: Term, v41: Term, a2: Term, v40: Term, a3: Term, a0: Term, v39: Term) -> CheckResult<Option<Term>> {
let v73 = match s.apply(v61, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v74, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v60, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v41, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Numeral(v81)) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v79, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v40, v84) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, a1, v85, v39)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v56: Term, v58: Term, v42: Term, a3: Term, a1: Term, v41: Term, a2: Term, v40: Term, a0: Term, v39: Term) -> CheckResult<Option<Term>> {
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v42, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Numeral(v66)) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v67]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(v69)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v65, v71) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v61, v72, a1, v60, v41, a2, v40, a3, a0, v39)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, v44: Term, v43: Term, v42: Term, a1: Term, v41: Term, a2: Term, v40: Term, v39: Term) -> CheckResult<Option<Term>> {
let v45 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(v48)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(v51)) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v50, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v47, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v43, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v56, v58, v42, a3, a1, v41, a2, v40, a0, v39)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v24: Term, a0: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
let v33 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(v33)) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v34 { return Ok(None); }
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_bvsmod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, v44, v43, v42, a1, v41, a2, v40, v39)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v16: Term, a3: Term, v17: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != a3 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
let v29 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v32 { return Ok(None); }
if v31 != a0 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v24, a0, a1, a3, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v16, a3, v17, a0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-smod-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_50_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_313_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsmod_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v20 { return Ok(None); }
more_50_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, a1: Term, v111: Term, v98: Term, v79: Term, v26: Term) -> CheckResult<Option<Term>> {
let v112 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v112, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v111, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v114, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v98, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v79, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v26, v117) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v118))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v80: Term, v97: Term, a2: Term, a1: Term, v79: Term, v26: Term) -> CheckResult<Option<Term>> {
let v98 = match s.apply(v80, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v100, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.literal(Lit::Numeral(v104)) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v105]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.literal(Lit::Numeral(v107)) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v106, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v103, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v99, v110) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, a1, v111, v98, v79, v26)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v83: Term, a0: Term, v82: Term, v81: Term, v80: Term, a2: Term, a1: Term, v79: Term, v26: Term) -> CheckResult<Option<Term>> {
let v84 = match s.apply(v83, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v82, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(v86)) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v87]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Numeral(v89)) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v88, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v85, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v81, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v93, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v80, v97, a2, a1, v79, v26)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v60: Term, v71: Term, a1: Term, v59: Term, v40: Term, v39: Term, a2: Term, a0: Term, v26: Term) -> CheckResult<Option<Term>> {
let v72 = match s.apply(v60, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v72, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v59, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v40, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v39, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v83, a0, v82, v81, v80, a2, a1, v79, v26)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v57: Term, a0: Term, v41: Term, a2: Term, a1: Term, v40: Term, v39: Term, v26: Term) -> CheckResult<Option<Term>> {
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v41, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(v65)) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(v68)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v64, v70) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v60, v71, a1, v59, v40, v39, a2, a0, v26)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, a2: Term, a0: Term, v43: Term, v42: Term, v41: Term, a1: Term, v40: Term, v39: Term, v26: Term) -> CheckResult<Option<Term>> {
let v44 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Numeral(v50)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v46, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v42, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v54, v56) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v57, a0, v41, a2, a1, v40, v39, v26)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v29: Term, a0: Term, v28: Term, v27: Term, a2: Term, a1: Term, v26: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v29, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(v32)) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(v35)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v31, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v27, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, a2, a0, v43, v42, v41, a1, v40, v39, v26)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvsrem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v29, a0, v28, v27, a2, a1, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v17, v19, v18, a0, v11, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-srem-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_51_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_314_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsrem_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fpf, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_51_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s: &mut Store, v28: Term, a1: Term, v25: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v19, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v18, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(v33)) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Numeral(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v32, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v17, v39) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v40))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s: &mut Store, v14: Term, a0: Term, a1: Term, v13: Term, a2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_zero_5fextend, &[v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v20, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(v26)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_zero_5fextend, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s, v28, a1, v25, v19, v18, v17)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvusubo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s, v14, a0, a1, v13, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-usubo-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_52_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_315_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fusubo_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fpf, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_52_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn cases_0_78_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_312_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_313_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_314_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_315_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v111: Term, v125: Term, v110: Term, v79: Term, v78: Term, v26: Term) -> CheckResult<Option<Term>> {
let v126 = match s.apply(v111, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v126, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v110, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v79, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v130, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v78, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v26, v133) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v134))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a2: Term, a0: Term, a1: Term, v111: Term, v110: Term, v79: Term, v78: Term, v26: Term) -> CheckResult<Option<Term>> {
let v112 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v114, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v113, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v112, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(v119)) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v121, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v118, v124) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v111, v125, v110, v79, v78, v26)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v95: Term, v97: Term, v94: Term, v93: Term, v80: Term, a2: Term, a0: Term, a1: Term, v79: Term, v78: Term, v26: Term) -> CheckResult<Option<Term>> {
let v98 = match s.apply(v95, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(v99)) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v100]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v98, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v94, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v106, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v93, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v80, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a2, a0, a1, v111, v110, v79, v78, v26)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v83: Term, a0: Term, v82: Term, v81: Term, a2: Term, a1: Term, v80: Term, v79: Term, v78: Term, v26: Term) -> CheckResult<Option<Term>> {
let v84 = match s.apply(v83, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v82, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(v86)) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v87]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Numeral(v89)) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v88, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v85, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v81, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v95, v97, v94, v93, v80, a2, a0, a1, v79, v78, v26)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v69: Term, v71: Term, v66: Term, v59: Term, v58: Term, v27: Term, a2: Term, a0: Term, a1: Term, v26: Term) -> CheckResult<Option<Term>> {
let v72 = match s.apply(v69, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v66, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v59, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v74, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v58, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v27, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v83, a0, v82, v81, a2, a1, v80, v79, v78, v26)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v28: Term, v57: Term, a2: Term, a0: Term, a1: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v58 = match s.apply(v28, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v61, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v60, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(v67)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Numeral(v70)) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v69, v71, v66, v59, v58, v27, a2, a0, a1, v26)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a2: Term, a1: Term, v43: Term, v42: Term, v41: Term, v28: Term, a0: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v44 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Numeral(v50)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v46, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v42, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v54, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v41, v56) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v28, v57, a2, a0, a1, v27, v26)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a2: Term, a0: Term, v29: Term, a1: Term, v28: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v33, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v29, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a2, a1, v43, v42, v41, v28, a0, v27, v26)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvssubo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a2, a0, v29, a1, v28, v27, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v17, v19, v18, a0, v11, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ssubo-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_53_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_316_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fssubo_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fpf, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_53_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, v27: Term, v45: Term, v25: Term) -> CheckResult<Option<Term>> {
let v46 = match s.apply(v27, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v25, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, v30: Term, v28: Term, a1: Term, v27: Term, v25: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(v32)) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v31, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v28, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(v38)) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v37, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v36, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Binary(BitVec::new(0, &v42))) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v35, v44) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, v27, v45, v25)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvnego, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(v29)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, v30, v28, a1, v27, v25)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a1 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, v17, v19, v18, a0, v11, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-nego-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_317_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fnego_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-equal-children"
pub fn eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren(s, a0, a1);
s.leave();
result
}
pub(super) fn case_318_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s: &mut Store, v9: Term, v15: Term, v0: Term, a0: Term) -> CheckResult<Option<Term>> {
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v0, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s, v9, v15, v0, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-const-children-1"
pub fn eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s, a0);
s.leave();
result
}
pub(super) fn case_319_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_79_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_316_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_317_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_318_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_319_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_19_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_76_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_77_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_78_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_79_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_4_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_16_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_17_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_18_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_19_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s: &mut Store, v9: Term, v15: Term, v0: Term, a0: Term) -> CheckResult<Option<Term>> {
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v0, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s, v9, v15, v0, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-const-children-2"
pub fn eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s, a0);
s.leave();
result
}
pub(super) fn case_320_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s: &mut Store, v11: Term, a1: Term, a3: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s, v11, a1, a3, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-equal-cond-1"
pub fn eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_321_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s: &mut Store, v11: Term, a1: Term, a3: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v3, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s, v11, a1, a3, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-equal-cond-2"
pub fn eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_322_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s: &mut Store, v7: Term, v11: Term, v0: Term, a0: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s, v7, v11, v0, a0, a1, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-equal-cond-3"
pub fn eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_323_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v18 = match eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3(s, v2, v5, v8, v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn cases_0_80_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_320_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_321_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_322_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_323_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s: &mut Store, v11: Term, a0: Term, a1: Term, v10: Term, a3: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Binary(BitVec::new(1, &v17))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v12, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v10, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v9, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s, v11, a0, a1, v10, a3, a2, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-merge-then-if"
pub fn eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_324_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s: &mut Store, v11: Term, a0: Term, a1: Term, v10: Term, a2: Term, a3: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Binary(BitVec::new(1, &v15))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v12, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v10, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v9, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s, v11, a0, a1, v10, a2, a3, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-merge-else-if"
pub fn eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_325_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, v24: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v9, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, a0: Term, v11: Term, a1: Term, v10: Term, a3: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Binary(BitVec::new(1, &v19))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v10, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a3) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s, v24, a2, v9)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v3, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s, a0, v11, a1, v10, a3, a2, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-merge-then-else"
pub fn eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_326_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s: &mut Store, a0: Term, v11: Term, a1: Term, v10: Term, a2: Term, a3: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Binary(BitVec::new(1, &v17))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v14, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v10, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v9, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v3, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s, a0, v11, a1, v10, a2, a3, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-merge-else-else"
pub fn eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_327_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v14 { return Ok(None); }
let v15 = match eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_81_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_324_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_325_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_326_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_327_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-shl-by-const-0"
pub fn eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0(s, a0, a1);
s.leave();
result
}
pub(super) fn case_328_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v77: Term, v71: Term, v65: Term) -> CheckResult<Option<Term>> {
let v78 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Binary(BitVec::new(0, &v78))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v77, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v71, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v65, v81) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v82))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v61: Term, v63: Term, v59: Term, a3: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v59, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(v67)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_extract, &[a3, v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v66, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(v74)) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v73, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v72, v76) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v77, v71, v65)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v43: Term, a1: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v50 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
if v55 != a1 { return Ok(None); }
let v57 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v58 { return Ok(None); }
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v61, v63, v59, a3, a0, a1)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a0 { return Ok(None); }
let v41 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v47 { return Ok(None); }
let v48 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(v48)) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v49 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v43, a1, a0, a2, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a5: Term, a3: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
if v28 != a3 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v34, v35, a0, v32, a1, a2, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v17, v19, v18, a0, v4, a5, a3, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-shl-by-const-1"
pub fn eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_54_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_329_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v20 { return Ok(None); }
more_54_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, a2: Term, a1: Term, v61: Term, v59: Term, a3: Term) -> CheckResult<Option<Term>> {
let v62 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v59, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(v67)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v66, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v65, v69) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v70))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, v47: Term, a3: Term, a0: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v48 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
if v53 != a3 { return Ok(None); }
let v55 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v56 != v58 { return Ok(None); }
if v57 != a0 { return Ok(None); }
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, a2, a1, v61, v59, a3)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a1: Term, v32: Term, a0: Term, v25: Term, a6: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v34 != v36 { return Ok(None); }
if v35 != a1 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a0 { return Ok(None); }
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
more_2_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, v47, a3, a0, a2, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a5: Term, a1: Term, a6: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v36 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, v34, v36, v35, a1, v32, a0, v25, a6, a3, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, v17, v19, v18, a0, v4, a5, a1, a6, a3, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-shl-by-const-2"
pub fn eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn more_55_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v15: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24eo_5fpf, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, v2, v5, v8, v11, v25, v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn case_330_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v20 else { return Ok(None); }
;
let v21 = fields[0];
let v22 = fields[1];
let v23 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_55_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v15, v18, v21, v2, v5, v8, v11)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-lshr-by-const-0"
pub fn eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0(s, a0, a1);
s.leave();
result
}
pub(super) fn case_331_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_82_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_328_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_329_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_330_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_331_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v59: Term, v55: Term, v49: Term) -> CheckResult<Option<Term>> {
let v60 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.literal(Lit::Binary(BitVec::new(0, &v60))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v55, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v49, v63) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v64))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v46: Term, a1: Term, v45: Term, v43: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v47 = match s.apply(v46, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v43, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Numeral(v52)) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v51, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v50, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_extract, &[a3, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v59, v55, v49)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a0 { return Ok(None); }
let v41 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(v41)) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v42 { return Ok(None); }
let v43 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v46, a1, v45, v43, a3, a0)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a5: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
if v28 != a3 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v34, v35, a0, v32, a2, a1, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v17, v19, v18, a0, v4, a5, a3, a2, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-lshr-by-const-1"
pub fn eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_56_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_332_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v20 { return Ok(None); }
more_56_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s: &mut Store, a0: Term, a2: Term, a1: Term, v46: Term) -> CheckResult<Option<Term>> {
let v47 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v48, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v46, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(v54)) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v53, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v52, v56) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v57))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a1: Term, v32: Term, a0: Term, v25: Term, a2: Term) -> CheckResult<Option<Term>> {
if v34 != v36 { return Ok(None); }
if v35 != a1 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a0 { return Ok(None); }
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v45 { return Ok(None); }
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, a0, a2, a1, v46)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
let v36 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, v34, v36, v35, a1, v32, a0, v25, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, v17, v19, v18, a0, v4, a4, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-lshr-by-const-2"
pub fn eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_57_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_333_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v17 { return Ok(None); }
let v18 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_57_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ashr-by-const-0"
pub fn eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0(s, a0, a1);
s.leave();
result
}
pub(super) fn case_334_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d0(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v56: Term, v58: Term, v55: Term, v49: Term) -> CheckResult<Option<Term>> {
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.literal(Lit::Binary(BitVec::new(0, &v60))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v55, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v49, v63) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v64))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v46: Term, a1: Term, v45: Term, v43: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v47 = match s.apply(v46, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v43, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_repeat, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v51, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v50, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_extract, &[a3, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v56, v58, v55, v49)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a0 { return Ok(None); }
let v41 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(v41)) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v42 { return Ok(None); }
let v43 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v46, a1, v45, v43, a3, a0)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a5: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
if v28 != a3 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v34, v35, a0, v32, a2, a1, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v17, v19, v18, a0, v4, a5, a3, a2, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ashr-by-const-1"
pub fn eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_58_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_335_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v20 { return Ok(None); }
more_58_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_83_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_332_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_333_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_334_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_335_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_20_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_80_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_81_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_82_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_83_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v87: Term, v91: Term) -> CheckResult<Option<Term>> {
let v92 = match s.apply(v87, v91) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v92))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v79: Term, a0: Term, a2: Term, a1: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
if v79 != a0 { return Ok(None); }
let v81 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v82, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v83, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v81, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_repeat, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v88, v90) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v87, v91)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v64: Term, a0: Term, v57: Term, a8: Term, a4: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v64 != a0 { return Ok(None); }
let v66 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Numeral(v66)) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v67 { return Ok(None); }
let v68 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v68 else { return Ok(None); }
;
let v69 = fields[0];
let v70 = match s.unapply(v69) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v71, v72)) = v70 else { return Ok(None); }
;
let v73 = match s.unapply(v71) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v74 != v76 { return Ok(None); }
if v75 != a4 { return Ok(None); }
let v77 = match s.unapply(v72) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v78, v79)) = v77 else { return Ok(None); }
;
let v80 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v78 != v80 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v79, a0, a2, a1, a4, a3)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v47: Term, a3: Term, a0: Term, a8: Term, a4: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v48 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
if v53 != a3 { return Ok(None); }
let v55 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
let v62 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v63 != v65 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v64, a0, v57, a8, a4, a2, a1, a3)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a1: Term, v32: Term, a0: Term, v25: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
if v34 != v36 { return Ok(None); }
if v35 != a1 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a0 { return Ok(None); }
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v47, a3, a0, a8, a4, a2, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a6: Term, a1: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
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
let v36 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v34, v36, v35, a1, v32, a0, v25, a7, a3, a8, a4, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v17, v19, v18, a0, v4, a6, a1, a7, a3, a8, a4, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ashr-by-const-2"
pub fn eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8);
s.leave();
result
}
pub(super) fn more_59_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v29 { return Ok(None); }
let v30 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__24eo_5fpf, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24eo_5fpf, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__24eo_5fpf, &[v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v2, v5, v8, v11, v14, v31, v33, v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn case_336_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v20 else { return Ok(None); }
;
let v21 = fields[0];
let v22 = fields[1];
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
more_59_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v133: Term, v142: Term, v132: Term, v130: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
let v143 = match eo__24eo_5fnil(s, v133, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v132, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v130, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v120, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Binary(BitVec::new(0, &v147))) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v146, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v119, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v87, v150) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v151))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v121: Term, v129: Term, a2: Term, a7: Term, a0: Term, a1: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
let v130 = match s.apply(v121, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v131, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.literal(Lit::Numeral(v134)) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_extract, &[a7, v135]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListConcat, &[v138, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.builtin_list(EvalOp::ListSingletonElim, &[v137, v139]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v136, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match eo__24eo_5ftypeof(s, v141) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v133, v142, v132, v130, v120, v119, v87)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v107: Term, v116: Term, v96: Term, v88: Term, a7: Term, a0: Term, a1: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v117 = match s.apply(v107, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v96, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v88, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_extract, &[a7, v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.builtin_list(EvalOp::ListConcat, &[v126, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.builtin_list(EvalOp::ListSingletonElim, &[v125, v127]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v124, v128) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v121, v129, a2, a7, a0, a1, v120, v119, v87)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v99: Term, a4: Term, v104: Term, v98: Term, v97: Term, a5: Term, a6: Term, a0: Term, a1: Term, v96: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v105 = match s.builtin_list(EvalOp::ListConcat, &[v99, a4, v104]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.builtin_list(EvalOp::ListSingletonElim, &[v98, v105]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v97, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_list(EvalOp::ListConcat, &[v111, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.builtin_list(EvalOp::ListSingletonElim, &[v110, v112]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v109, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24eo_5ftypeof(s, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match eo__24eo_5fnil(s, v108, v115) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v107, v116, v96, v88, a7, a0, a1, a2, v87)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v91: Term, v90: Term, v89: Term, a3: Term, a4: Term, a5: Term, a6: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v92 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.builtin_list(EvalOp::ListConcat, &[v92, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.builtin_list(EvalOp::ListSingletonElim, &[v91, v93]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v90, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v89, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v100, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Binary(BitVec::new(0, &v102))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v99, a4, v104, v98, v97, a5, a6, a0, a1, v96, v88, a7, a2, v87)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v78: Term, v76: Term, v74: Term, a4: Term, v73: Term, a1: Term, v72: Term, a0: Term, v71: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term) -> CheckResult<Option<Term>> {
let v79 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Binary(BitVec::new(0, &v79))) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v76, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListConcat, &[v74, a4, v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v73, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.builtin_list(EvalOp::ListConcat, &[v72, a0, v85]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v71, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, a0, a1, v91, v90, v89, a3, a4, a5, a6, v88, a7, a2, v87)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v66: Term, v68: Term, v67: Term, a2: Term, v60: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v66 != v68 { return Ok(None); }
if v67 != a2 { return Ok(None); }
let v69 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(v69)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v70 { return Ok(None); }
let v71 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v78, v76, v74, a4, v73, a1, v72, a0, v71, a5, a6, a3, a7, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a10: Term, a7: Term, a2: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v49 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v49 else { return Ok(None); }
;
let v50 = fields[0];
let v51 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
if v56 != a7 { return Ok(None); }
let v58 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v66, v68, v67, a2, v60, a3, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v34: Term, a3: Term, v35: Term, a2: Term, a4: Term, v24: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v36 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v39 { return Ok(None); }
if v38 != a3 { return Ok(None); }
let v40 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a2 { return Ok(None); }
if v42 != a4 { return Ok(None); }
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v48 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, a10, a7, a2, a3, a4, a1, a0, a5, a6)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v16: Term, a5: Term, v17: Term, a3: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != a5 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
let v29 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v32 { return Ok(None); }
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v34, a3, v35, a2, a4, v24, a10, a7, a1, a0, a5, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a6 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v16, a5, v17, a3, a2, a4, a10, a7, a1, a0, a6)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-and-concat-pullup"
pub fn eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_60_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v2, v5, v8, v11, v14, v17, v20, v23, v37, v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_337_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v25 { return Ok(None); }
more_60_eo__24eo_5fcmd_5fstep_5fproven(s, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v133: Term, v142: Term, v132: Term, v130: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
let v143 = match eo__24eo_5fnil(s, v133, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v132, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v130, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v120, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Binary(BitVec::new(0, &v147))) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v146, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v119, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v87, v150) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v151))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v121: Term, v129: Term, a2: Term, a7: Term, a0: Term, a1: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
let v130 = match s.apply(v121, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v131, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.literal(Lit::Numeral(v134)) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_extract, &[a7, v135]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListConcat, &[v138, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.builtin_list(EvalOp::ListSingletonElim, &[v137, v139]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v136, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match eo__24eo_5ftypeof(s, v141) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v133, v142, v132, v130, v120, v119, v87)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v107: Term, v116: Term, v96: Term, v88: Term, a7: Term, a0: Term, a1: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v117 = match s.apply(v107, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v96, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v88, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_extract, &[a7, v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.builtin_list(EvalOp::ListConcat, &[v126, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.builtin_list(EvalOp::ListSingletonElim, &[v125, v127]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v124, v128) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v121, v129, a2, a7, a0, a1, v120, v119, v87)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v99: Term, a4: Term, v104: Term, v98: Term, v97: Term, a5: Term, a6: Term, a0: Term, a1: Term, v96: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v105 = match s.builtin_list(EvalOp::ListConcat, &[v99, a4, v104]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.builtin_list(EvalOp::ListSingletonElim, &[v98, v105]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v97, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_list(EvalOp::ListConcat, &[v111, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.builtin_list(EvalOp::ListSingletonElim, &[v110, v112]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v109, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24eo_5ftypeof(s, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match eo__24eo_5fnil(s, v108, v115) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v107, v116, v96, v88, a7, a0, a1, a2, v87)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v91: Term, v90: Term, v89: Term, a3: Term, a4: Term, a5: Term, a6: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v92 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.builtin_list(EvalOp::ListConcat, &[v92, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.builtin_list(EvalOp::ListSingletonElim, &[v91, v93]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v90, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v89, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v100, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Binary(BitVec::new(0, &v102))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v99, a4, v104, v98, v97, a5, a6, a0, a1, v96, v88, a7, a2, v87)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v78: Term, v76: Term, v74: Term, a4: Term, v73: Term, a1: Term, v72: Term, a0: Term, v71: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term) -> CheckResult<Option<Term>> {
let v79 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Binary(BitVec::new(0, &v79))) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v76, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListConcat, &[v74, a4, v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v73, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.builtin_list(EvalOp::ListConcat, &[v72, a0, v85]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v71, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, a0, a1, v91, v90, v89, a3, a4, a5, a6, v88, a7, a2, v87)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v66: Term, v68: Term, v67: Term, a2: Term, v60: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v66 != v68 { return Ok(None); }
if v67 != a2 { return Ok(None); }
let v69 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(v69)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v70 { return Ok(None); }
let v71 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v78, v76, v74, a4, v73, a1, v72, a0, v71, a5, a6, a3, a7, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a10: Term, a7: Term, a2: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v49 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v49 else { return Ok(None); }
;
let v50 = fields[0];
let v51 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
if v56 != a7 { return Ok(None); }
let v58 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v66, v68, v67, a2, v60, a3, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v34: Term, a3: Term, v35: Term, a2: Term, a4: Term, v24: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v36 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v39 { return Ok(None); }
if v38 != a3 { return Ok(None); }
let v40 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a2 { return Ok(None); }
if v42 != a4 { return Ok(None); }
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v48 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, a10, a7, a2, a3, a4, a1, a0, a5, a6)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v16: Term, a5: Term, v17: Term, a3: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != a5 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
let v29 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v32 { return Ok(None); }
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v34, a3, v35, a2, a4, v24, a10, a7, a1, a0, a5, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a6 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v16, a5, v17, a3, a2, a4, a10, a7, a1, a0, a6)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-or-concat-pullup"
pub fn eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_61_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v2, v5, v8, v11, v14, v17, v20, v23, v37, v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_338_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v25 { return Ok(None); }
more_61_eo__24eo_5fcmd_5fstep_5fproven(s, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v133: Term, v142: Term, v132: Term, v130: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
let v143 = match eo__24eo_5fnil(s, v133, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v132, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v130, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v120, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Binary(BitVec::new(0, &v147))) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v146, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v119, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v87, v150) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v151))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v121: Term, v129: Term, a2: Term, a7: Term, a0: Term, a1: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
let v130 = match s.apply(v121, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v131, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.literal(Lit::Numeral(v134)) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_extract, &[a7, v135]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListConcat, &[v138, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.builtin_list(EvalOp::ListSingletonElim, &[v137, v139]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v136, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match eo__24eo_5ftypeof(s, v141) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v133, v142, v132, v130, v120, v119, v87)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v107: Term, v116: Term, v96: Term, v88: Term, a7: Term, a0: Term, a1: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v117 = match s.apply(v107, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v96, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v88, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_extract, &[a7, v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.builtin_list(EvalOp::ListConcat, &[v126, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.builtin_list(EvalOp::ListSingletonElim, &[v125, v127]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v124, v128) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v121, v129, a2, a7, a0, a1, v120, v119, v87)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v99: Term, a4: Term, v104: Term, v98: Term, v97: Term, a5: Term, a6: Term, a0: Term, a1: Term, v96: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v105 = match s.builtin_list(EvalOp::ListConcat, &[v99, a4, v104]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.builtin_list(EvalOp::ListSingletonElim, &[v98, v105]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v97, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_list(EvalOp::ListConcat, &[v111, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.builtin_list(EvalOp::ListSingletonElim, &[v110, v112]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v109, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24eo_5ftypeof(s, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match eo__24eo_5fnil(s, v108, v115) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v107, v116, v96, v88, a7, a0, a1, a2, v87)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v91: Term, v90: Term, v89: Term, a3: Term, a4: Term, a5: Term, a6: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
let v92 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.builtin_list(EvalOp::ListConcat, &[v92, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.builtin_list(EvalOp::ListSingletonElim, &[v91, v93]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v90, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v89, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v100, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Binary(BitVec::new(0, &v102))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v99, a4, v104, v98, v97, a5, a6, a0, a1, v96, v88, a7, a2, v87)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v78: Term, v76: Term, v74: Term, a4: Term, v73: Term, a1: Term, v72: Term, a0: Term, v71: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term) -> CheckResult<Option<Term>> {
let v79 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Binary(BitVec::new(0, &v79))) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v76, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListConcat, &[v74, a4, v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v73, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.builtin_list(EvalOp::ListConcat, &[v72, a0, v85]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v71, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, a0, a1, v91, v90, v89, a3, a4, a5, a6, v88, a7, a2, v87)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v66: Term, v68: Term, v67: Term, a2: Term, v60: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v66 != v68 { return Ok(None); }
if v67 != a2 { return Ok(None); }
let v69 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(v69)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v70 { return Ok(None); }
let v71 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v78, v76, v74, a4, v73, a1, v72, a0, v71, a5, a6, a3, a7, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a10: Term, a7: Term, a2: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v49 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v49 else { return Ok(None); }
;
let v50 = fields[0];
let v51 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
if v56 != a7 { return Ok(None); }
let v58 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v66, v68, v67, a2, v60, a3, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v34: Term, a3: Term, v35: Term, a2: Term, a4: Term, v24: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v36 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v39 { return Ok(None); }
if v38 != a3 { return Ok(None); }
let v40 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a2 { return Ok(None); }
if v42 != a4 { return Ok(None); }
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v48 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, a10, a7, a2, a3, a4, a1, a0, a5, a6)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v16: Term, a5: Term, v17: Term, a3: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != a5 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
let v29 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v32 { return Ok(None); }
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v34, a3, v35, a2, a4, v24, a10, a7, a1, a0, a5, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a6 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v16, a5, v17, a3, a2, a4, a10, a7, a1, a0, a6)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-concat-pullup"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_62_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v2, v5, v8, v11, v14, v17, v20, v23, v37, v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_339_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v25 { return Ok(None); }
more_62_eo__24eo_5fcmd_5fstep_5fproven(s, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23)
}
pub(super) fn cases_0_84_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_336_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_337_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_338_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_339_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v156: Term, v191: Term, v133: Term) -> CheckResult<Option<Term>> {
let v192 = match s.apply(v156, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v133, v192) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v193))
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v178: Term, v175: Term, v174: Term, v167: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
let v179 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.builtin_list(EvalOp::ListConcat, &[v180, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.builtin_list(EvalOp::ListSingletonElim, &[v179, v181]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v178, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match eo__24eo_5ftypeof(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match eo__24eo_5fnil(s, v175, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v174, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v167, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v157, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Binary(BitVec::new(0, &v189))) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v188, v190) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v156, v191, v133)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v161: Term, v165: Term, v158: Term, a2: Term, a4: Term, a7: Term, a0: Term, a1: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
let v166 = match s.apply(v161, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v158, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.builtin_list(EvalOp::ListSingletonElim, &[v169, v172]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v168, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(v176)) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_extract, &[a7, v177]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, a0, a1, v178, v175, v174, v167, v157, v156, v133)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v145: Term, v152: Term, v144: Term, v142: Term, v134: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
let v153 = match eo__24eo_5fnil(s, v145, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v144, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v142, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v134, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.literal(Lit::Numeral(v159)) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo_extract, &[a7, v160]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.builtin_list(EvalOp::ListConcat, &[v163, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.builtin_list(EvalOp::ListSingletonElim, &[v162, v164]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v161, v165, v158, a2, a4, a7, a0, a1, v157, v156, v133)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v136: Term, v140: Term, v135: Term, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v134: Term, a7: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
let v141 = match s.apply(v136, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v135, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.builtin_list(EvalOp::ListConcat, &[v148, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.builtin_list(EvalOp::ListSingletonElim, &[v147, v149]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v146, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match eo__24eo_5ftypeof(s, v151) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v145, v152, v144, v142, v134, a7, a0, a1, a2, a4, v133)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v125: Term, v128: Term, v123: Term, a1: Term, v122: Term, a0: Term, v121: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v129 = match s.apply(v125, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v123, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_list(EvalOp::ListConcat, &[v122, a0, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v121, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListConcat, &[v138, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.builtin_list(EvalOp::ListSingletonElim, &[v137, v139]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v136, v140, v135, a3, a5, a6, a0, a1, v134, a7, a2, a4, v133)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v116: Term, v118: Term, v117: Term, a3: Term, v85: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v116 != v118 { return Ok(None); }
if v117 != a3 { return Ok(None); }
let v119 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(v119)) { Ok(v) => v, Err(e) => return Err(e) };
if v85 != v120 { return Ok(None); }
let v121 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v127, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v125, v128, v123, a1, v122, a0, v121, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v102: Term, a3: Term, v103: Term, a2: Term, a4: Term, v92: Term, v85: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v104 = match s.unapply(v102) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v105, v106)) = v104 else { return Ok(None); }
;
let v107 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v105 != v107 { return Ok(None); }
if v106 != a3 { return Ok(None); }
let v108 = match s.unapply(v103) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v109, v110)) = v108 else { return Ok(None); }
;
let v111 = match s.unapply(v109) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v112, v113)) = v111 else { return Ok(None); }
;
let v114 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v112 != v114 { return Ok(None); }
if v113 != a2 { return Ok(None); }
if v110 != a4 { return Ok(None); }
let v115 = match s.unapply(v92) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v116, v117)) = v115 else { return Ok(None); }
;
let v118 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v116, v118, v117, a3, v85, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v78: Term, a3: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v83 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v87, v88)) = v86 else { return Ok(None); }
;
let v89 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v87 != v89 { return Ok(None); }
let v90 = match s.unapply(v88) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v94, v95)) = v93 else { return Ok(None); }
;
let v96 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v96 { return Ok(None); }
let v97 = match s.unapply(v95) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v98, v99)) = v97 else { return Ok(None); }
;
let v100 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v98 != v100 { return Ok(None); }
let v101 = match s.unapply(v99) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v102, v103)) = v101 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v102, a3, v103, a2, a4, v92, v85, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v71 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a2 { return Ok(None); }
if v67 != a4 { return Ok(None); }
let v72 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Numeral(v72)) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v73 { return Ok(None); }
let v74 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v74 else { return Ok(None); }
;
let v75 = fields[0];
let v76 = match s.unapply(v75) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v80, v81)) = v79 else { return Ok(None); }
;
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v80 != v82 { return Ok(None); }
if v81 != a7 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v78, a3, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v51: Term, v52: Term, a3: Term, a2: Term, a4: Term, v49: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v53 { return Ok(None); }
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
if v63 != a3 { return Ok(None); }
let v65 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v69, v70, a2, v67, a4, v49, a10, a7, a3, a1, a0, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v11: Term, a3: Term, a9: Term, a5: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
let v34 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a3 { return Ok(None); }
let v38 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
let v40 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a5 { return Ok(None); }
let v47 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.unapply(v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v51, v52, a3, a2, a4, v49, a10, a7, a1, a0, a5, a6)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v17: Term, v19: Term, v18: Term, a3: Term, a2: Term, a4: Term, v11: Term, a9: Term, a5: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a3 { return Ok(None); }
let v27 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a2 { return Ok(None); }
if v29 != a4 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v11, a3, a9, a5, a2, a4, a10, a7, a1, a0, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a6 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v17, v19, v18, a3, a2, a4, v11, a9, a5, a10, a7, a1, a0, a6)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-and-concat-pullup2"
pub fn eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_63_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v2, v5, v8, v11, v14, v17, v20, v23, v37, v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_340_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v25 { return Ok(None); }
more_63_eo__24eo_5fcmd_5fstep_5fproven(s, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v156: Term, v191: Term, v133: Term) -> CheckResult<Option<Term>> {
let v192 = match s.apply(v156, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v133, v192) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v193))
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v178: Term, v175: Term, v174: Term, v167: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
let v179 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.builtin_list(EvalOp::ListConcat, &[v180, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.builtin_list(EvalOp::ListSingletonElim, &[v179, v181]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v178, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match eo__24eo_5ftypeof(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match eo__24eo_5fnil(s, v175, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v174, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v167, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v157, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Binary(BitVec::new(0, &v189))) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v188, v190) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v156, v191, v133)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v161: Term, v165: Term, v158: Term, a2: Term, a4: Term, a7: Term, a0: Term, a1: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
let v166 = match s.apply(v161, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v158, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.builtin_list(EvalOp::ListSingletonElim, &[v169, v172]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v168, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(v176)) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_extract, &[a7, v177]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, a0, a1, v178, v175, v174, v167, v157, v156, v133)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v145: Term, v152: Term, v144: Term, v142: Term, v134: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
let v153 = match eo__24eo_5fnil(s, v145, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v144, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v142, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v134, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.literal(Lit::Numeral(v159)) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo_extract, &[a7, v160]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.builtin_list(EvalOp::ListConcat, &[v163, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.builtin_list(EvalOp::ListSingletonElim, &[v162, v164]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v161, v165, v158, a2, a4, a7, a0, a1, v157, v156, v133)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v136: Term, v140: Term, v135: Term, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v134: Term, a7: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
let v141 = match s.apply(v136, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v135, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.builtin_list(EvalOp::ListConcat, &[v148, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.builtin_list(EvalOp::ListSingletonElim, &[v147, v149]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v146, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match eo__24eo_5ftypeof(s, v151) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v145, v152, v144, v142, v134, a7, a0, a1, a2, a4, v133)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v125: Term, v128: Term, v123: Term, a1: Term, v122: Term, a0: Term, v121: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v129 = match s.apply(v125, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v123, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_list(EvalOp::ListConcat, &[v122, a0, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v121, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListConcat, &[v138, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.builtin_list(EvalOp::ListSingletonElim, &[v137, v139]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v136, v140, v135, a3, a5, a6, a0, a1, v134, a7, a2, a4, v133)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v116: Term, v118: Term, v117: Term, a3: Term, v85: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v116 != v118 { return Ok(None); }
if v117 != a3 { return Ok(None); }
let v119 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(v119)) { Ok(v) => v, Err(e) => return Err(e) };
if v85 != v120 { return Ok(None); }
let v121 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v127, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v125, v128, v123, a1, v122, a0, v121, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v102: Term, a3: Term, v103: Term, a2: Term, a4: Term, v92: Term, v85: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v104 = match s.unapply(v102) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v105, v106)) = v104 else { return Ok(None); }
;
let v107 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v105 != v107 { return Ok(None); }
if v106 != a3 { return Ok(None); }
let v108 = match s.unapply(v103) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v109, v110)) = v108 else { return Ok(None); }
;
let v111 = match s.unapply(v109) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v112, v113)) = v111 else { return Ok(None); }
;
let v114 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v112 != v114 { return Ok(None); }
if v113 != a2 { return Ok(None); }
if v110 != a4 { return Ok(None); }
let v115 = match s.unapply(v92) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v116, v117)) = v115 else { return Ok(None); }
;
let v118 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v116, v118, v117, a3, v85, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v78: Term, a3: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v83 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v87, v88)) = v86 else { return Ok(None); }
;
let v89 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v87 != v89 { return Ok(None); }
let v90 = match s.unapply(v88) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v94, v95)) = v93 else { return Ok(None); }
;
let v96 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v96 { return Ok(None); }
let v97 = match s.unapply(v95) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v98, v99)) = v97 else { return Ok(None); }
;
let v100 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v98 != v100 { return Ok(None); }
let v101 = match s.unapply(v99) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v102, v103)) = v101 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v102, a3, v103, a2, a4, v92, v85, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v71 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a2 { return Ok(None); }
if v67 != a4 { return Ok(None); }
let v72 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Numeral(v72)) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v73 { return Ok(None); }
let v74 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v74 else { return Ok(None); }
;
let v75 = fields[0];
let v76 = match s.unapply(v75) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v80, v81)) = v79 else { return Ok(None); }
;
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v80 != v82 { return Ok(None); }
if v81 != a7 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v78, a3, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v51: Term, v52: Term, a3: Term, a2: Term, a4: Term, v49: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v53 { return Ok(None); }
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
if v63 != a3 { return Ok(None); }
let v65 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v69, v70, a2, v67, a4, v49, a10, a7, a3, a1, a0, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v11: Term, a3: Term, a9: Term, a5: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
let v34 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a3 { return Ok(None); }
let v38 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
let v40 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a5 { return Ok(None); }
let v47 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.unapply(v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v51, v52, a3, a2, a4, v49, a10, a7, a1, a0, a5, a6)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v17: Term, v19: Term, v18: Term, a3: Term, a2: Term, a4: Term, v11: Term, a9: Term, a5: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a3 { return Ok(None); }
let v27 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a2 { return Ok(None); }
if v29 != a4 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v11, a3, a9, a5, a2, a4, a10, a7, a1, a0, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a6 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v17, v19, v18, a3, a2, a4, v11, a9, a5, a10, a7, a1, a0, a6)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-or-concat-pullup2"
pub fn eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_64_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v2, v5, v8, v11, v14, v17, v20, v23, v37, v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_341_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v25 { return Ok(None); }
more_64_eo__24eo_5fcmd_5fstep_5fproven(s, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v156: Term, v191: Term, v133: Term) -> CheckResult<Option<Term>> {
let v192 = match s.apply(v156, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v133, v192) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v193))
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v178: Term, v175: Term, v174: Term, v167: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
let v179 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.builtin_list(EvalOp::ListConcat, &[v180, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.builtin_list(EvalOp::ListSingletonElim, &[v179, v181]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v178, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match eo__24eo_5ftypeof(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match eo__24eo_5fnil(s, v175, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v174, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v167, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v157, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Binary(BitVec::new(0, &v189))) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v188, v190) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v156, v191, v133)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v161: Term, v165: Term, v158: Term, a2: Term, a4: Term, a7: Term, a0: Term, a1: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
let v166 = match s.apply(v161, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v158, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.builtin_list(EvalOp::ListSingletonElim, &[v169, v172]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v168, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(v176)) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_extract, &[a7, v177]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, a0, a1, v178, v175, v174, v167, v157, v156, v133)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v145: Term, v152: Term, v144: Term, v142: Term, v134: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
let v153 = match eo__24eo_5fnil(s, v145, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v144, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v142, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v134, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.literal(Lit::Numeral(v159)) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo_extract, &[a7, v160]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.builtin_list(EvalOp::ListConcat, &[v163, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.builtin_list(EvalOp::ListSingletonElim, &[v162, v164]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v161, v165, v158, a2, a4, a7, a0, a1, v157, v156, v133)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v136: Term, v140: Term, v135: Term, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v134: Term, a7: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
let v141 = match s.apply(v136, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v135, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.builtin_list(EvalOp::ListConcat, &[v148, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.builtin_list(EvalOp::ListSingletonElim, &[v147, v149]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v146, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match eo__24eo_5ftypeof(s, v151) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v145, v152, v144, v142, v134, a7, a0, a1, a2, a4, v133)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v125: Term, v128: Term, v123: Term, a1: Term, v122: Term, a0: Term, v121: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v129 = match s.apply(v125, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v123, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_list(EvalOp::ListConcat, &[v122, a0, v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v121, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListConcat, &[v138, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.builtin_list(EvalOp::ListSingletonElim, &[v137, v139]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v136, v140, v135, a3, a5, a6, a0, a1, v134, a7, a2, a4, v133)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v116: Term, v118: Term, v117: Term, a3: Term, v85: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v116 != v118 { return Ok(None); }
if v117 != a3 { return Ok(None); }
let v119 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(v119)) { Ok(v) => v, Err(e) => return Err(e) };
if v85 != v120 { return Ok(None); }
let v121 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v127, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v125, v128, v123, a1, v122, a0, v121, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v102: Term, a3: Term, v103: Term, a2: Term, a4: Term, v92: Term, v85: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v104 = match s.unapply(v102) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v105, v106)) = v104 else { return Ok(None); }
;
let v107 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v105 != v107 { return Ok(None); }
if v106 != a3 { return Ok(None); }
let v108 = match s.unapply(v103) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v109, v110)) = v108 else { return Ok(None); }
;
let v111 = match s.unapply(v109) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v112, v113)) = v111 else { return Ok(None); }
;
let v114 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v112 != v114 { return Ok(None); }
if v113 != a2 { return Ok(None); }
if v110 != a4 { return Ok(None); }
let v115 = match s.unapply(v92) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v116, v117)) = v115 else { return Ok(None); }
;
let v118 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v116, v118, v117, a3, v85, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v78: Term, a3: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v83 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v87, v88)) = v86 else { return Ok(None); }
;
let v89 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v87 != v89 { return Ok(None); }
let v90 = match s.unapply(v88) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v94, v95)) = v93 else { return Ok(None); }
;
let v96 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v96 { return Ok(None); }
let v97 = match s.unapply(v95) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v98, v99)) = v97 else { return Ok(None); }
;
let v100 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v98 != v100 { return Ok(None); }
let v101 = match s.unapply(v99) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v102, v103)) = v101 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v102, a3, v103, a2, a4, v92, v85, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v71 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a2 { return Ok(None); }
if v67 != a4 { return Ok(None); }
let v72 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Numeral(v72)) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v73 { return Ok(None); }
let v74 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v74 else { return Ok(None); }
;
let v75 = fields[0];
let v76 = match s.unapply(v75) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v80, v81)) = v79 else { return Ok(None); }
;
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v80 != v82 { return Ok(None); }
if v81 != a7 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v78, a3, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v51: Term, v52: Term, a3: Term, a2: Term, a4: Term, v49: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v53 { return Ok(None); }
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
if v63 != a3 { return Ok(None); }
let v65 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v69, v70, a2, v67, a4, v49, a10, a7, a3, a1, a0, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v11: Term, a3: Term, a9: Term, a5: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
let v34 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a3 { return Ok(None); }
let v38 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
let v40 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a5 { return Ok(None); }
let v47 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.unapply(v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v51, v52, a3, a2, a4, v49, a10, a7, a1, a0, a5, a6)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v17: Term, v19: Term, v18: Term, a3: Term, a2: Term, a4: Term, v11: Term, a9: Term, a5: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a3 { return Ok(None); }
let v27 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a2 { return Ok(None); }
if v29 != a4 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v11, a3, a9, a5, a2, a4, a10, a7, a1, a0, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a6 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v17, v19, v18, a3, a2, a4, v11, a9, a5, a10, a7, a1, a0, a6)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-concat-pullup2"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_65_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v2, v5, v8, v11, v14, v17, v20, v23, v37, v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_342_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v25 { return Ok(None); }
more_65_eo__24eo_5fcmd_5fstep_5fproven(s, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v237: Term, v251: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v252 = match s.apply(v237, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v227, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Binary(BitVec::new(0, &v254))) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v253, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v226, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v203, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v180, v258) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v259))
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v238: Term, a4: Term, a9: Term, a0: Term, a1: Term, v237: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v239 = match s.apply(v238, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.literal(Lit::Numeral(v241)) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_extract, &[a9, v242]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.builtin_list(EvalOp::ListConcat, &[v245, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.builtin_list(EvalOp::ListSingletonElim, &[v244, v246]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v243, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match eo__24eo_5ftypeof(s, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match eo__24eo_5fnil(s, v240, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v239, v250) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v237, v251, v227, v226, v203, v180)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v204: Term, v225: Term, a9: Term, a0: Term, a1: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v226 = match s.apply(v204, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(v229)) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_extract, &[a9, v230]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.builtin_list(EvalOp::ListConcat, &[v233, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.builtin_list(EvalOp::ListSingletonElim, &[v232, v234]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v231, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v228, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v238, a4, a9, a0, a1, v237, v227, v226, v203, v180)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v213: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v212: Term, v204: Term, a9: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v214 = match s.apply(v213, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.builtin_list(EvalOp::ListConcat, &[v218, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.builtin_list(EvalOp::ListSingletonElim, &[v217, v219]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v216, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24eo_5ftypeof(s, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match eo__24eo_5fnil(s, v215, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v214, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v212, v224) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v204, v225, a9, a0, a1, a4, v203, v180)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v189: Term, v201: Term, v181: Term, a7: Term, a8: Term, a0: Term, a1: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
let v202 = match s.apply(v189, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v181, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.builtin_list(EvalOp::ListConcat, &[v208, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_list(EvalOp::ListSingletonElim, &[v207, v209]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v206, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v205, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v213, a2, a7, a8, a0, a1, v212, v204, a9, a4, v203, v180)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v189: Term, v181: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
let v190 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v190, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.builtin_list(EvalOp::ListConcat, &[v195, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_list(EvalOp::ListSingletonElim, &[v194, v196]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v193, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match eo__24eo_5ftypeof(s, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match eo__24eo_5fnil(s, v192, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v191, v200) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v189, v201, v181, a7, a8, a0, a1, a2, a9, a4, v180)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v177: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a3: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term) -> CheckResult<Option<Term>> {
let v178 = match s.apply(v177, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_list(EvalOp::ListConcat, &[v164, a0, v178]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v163, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.builtin_list(EvalOp::ListConcat, &[v185, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.builtin_list(EvalOp::ListSingletonElim, &[v184, v186]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v183, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v182, v188) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v189, v181, a7, a8, a2, a9, a4, v180)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v165 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v166, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.literal(Lit::Binary(BitVec::new(0, &v172))) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v171, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v169, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v167, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v165, v176) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v177, a1, v164, a0, v163, a5, a6, a3, a7, a8, a2, a9, a4)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v145: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v150 = match s.unapply(v145) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v151, v152)) = v150 else { return Ok(None); }
;
let v153 = match s.unapply(v151) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v154, v155)) = v153 else { return Ok(None); }
;
let v156 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v154 != v156 { return Ok(None); }
let v157 = match s.unapply(v155) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v158, v159)) = v157 else { return Ok(None); }
;
let v160 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v158 != v160 { return Ok(None); }
if v159 != a4 { return Ok(None); }
let v161 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.literal(Lit::Numeral(v161)) { Ok(v) => v, Err(e) => return Err(e) };
if v152 != v162 { return Ok(None); }
let v163 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a3, a2, a4, a1, v164, a0, v163, a5, a6, a7, a8, a9)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v134: Term, v136: Term, v135: Term, a8: Term, v132: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v134 != v136 { return Ok(None); }
if v135 != a8 { return Ok(None); }
let v137 = match s.unapply(v132) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v138, v139)) = v137 else { return Ok(None); }
;
let v140 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v138 != v140 { return Ok(None); }
if v139 != a4 { return Ok(None); }
let v141 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v141 else { return Ok(None); }
;
let v142 = fields[0];
let v143 = match s.unapply(v142) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v144, v145)) = v143 else { return Ok(None); }
;
let v146 = match s.unapply(v144) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v147, v148)) = v146 else { return Ok(None); }
;
let v149 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v147 != v149 { return Ok(None); }
if v148 != a9 { return Ok(None); }
more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v145, a4, a3, a2, a1, a0, a5, a6, a7, a8, a9)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v118: Term, a4: Term, v115: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v120 = match s.unapply(v118) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v121, v122)) = v120 else { return Ok(None); }
;
let v123 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v121 != v123 { return Ok(None); }
if v122 != a4 { return Ok(None); }
let v124 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(v124)) { Ok(v) => v, Err(e) => return Err(e) };
if v115 != v125 { return Ok(None); }
let v126 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(v126)) { Ok(v) => v, Err(e) => return Err(e) };
if v97 != v127 { return Ok(None); }
let v128 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v128 else { return Ok(None); }
;
let v129 = fields[0];
let v130 = match s.unapply(v129) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v131, v132)) = v130 else { return Ok(None); }
;
let v133 = match s.unapply(v131) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v134, v135)) = v133 else { return Ok(None); }
;
let v136 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v134, v136, v135, a8, v132, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v100: Term, a2: Term, a4: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.unapply(v103) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v106, v107)) = v105 else { return Ok(None); }
;
let v108 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v106 != v108 { return Ok(None); }
let v109 = match s.unapply(v107) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v110, v111)) = v109 else { return Ok(None); }
;
let v112 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v110 != v112 { return Ok(None); }
if v111 != a2 { return Ok(None); }
let v113 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.unapply(v114) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v117, v118)) = v116 else { return Ok(None); }
;
let v119 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v117 != v119 { return Ok(None); }
more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v118, a4, v115, v97, a13, a8, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v75: Term, a12: Term, a7: Term, a2: Term, a4: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v84 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Numeral(v84)) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v85 { return Ok(None); }
let v86 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v86 else { return Ok(None); }
;
let v87 = fields[0];
let v88 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v92, v93)) = v91 else { return Ok(None); }
;
let v94 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v92 != v94 { return Ok(None); }
if v93 != a7 { return Ok(None); }
let v95 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.unapply(v96) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v99, v100)) = v98 else { return Ok(None); }
;
let v101 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v99 != v101 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v100, a2, a4, v97, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v67: Term, a2: Term, v64: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
if v71 != a2 { return Ok(None); }
let v73 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v77 != v79 { return Ok(None); }
let v80 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v81 != v83 { return Ok(None); }
if v82 != a4 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v75, a12, a7, a2, a4, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v11: Term, a11: Term, a6: Term, a2: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v51 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(v51)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v52 { return Ok(None); }
let v53 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v53 else { return Ok(None); }
;
let v54 = fields[0];
let v55 = match s.unapply(v54) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a6 { return Ok(None); }
let v62 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v66 != v68 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v67, a2, v64, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v35: Term, v37: Term, v36: Term, a2: Term, v29: Term, a3: Term, v11: Term, a11: Term, a6: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
if v35 != v37 { return Ok(None); }
if v36 != a2 { return Ok(None); }
let v38 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != a3 { return Ok(None); }
let v49 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Numeral(v49)) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v50 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v11, a11, a6, a2, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v20: Term, v21: Term, a4: Term, v18: Term, a2: Term, a3: Term, v11: Term, a11: Term, a6: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a4 { return Ok(None); }
let v27 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v35, v37, v36, a2, v29, a3, v11, a11, a6, a4, a12, a7, a13, a8, a14, a9, a1, a0, a5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a5 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v20, v21, a4, v18, a2, a3, v11, a11, a6, a12, a7, a13, a8, a14, a9, a1, a0, a5)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
let stuck8 = match s.is_stuck(a8) { Ok(v) => v, Err(e) => return Err(e) };
if stuck8 { return Ok(s.stuck()); }
let stuck9 = match s.is_stuck(a9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck9 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-and-concat-pullup3"
pub fn eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
s.leave();
result
}
pub(super) fn more_67_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v50: Term, a0: Term, v39: Term, v42: Term, v45: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term, v49: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo__24eo_5fpf, &[v50]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo__24eo_5fpf, &[v52]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__24eo_5fpf, &[v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__24eo_5fpf, &[v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49, v51, v53, v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn more_66_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v30: Term, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v31 { return Ok(None); }
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v35 else { return Ok(None); }
;
let v36 = fields[0];
let v37 = fields[1];
let v38 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
let v40 = fields[1];
let v41 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v41 else { return Ok(None); }
;
let v42 = fields[0];
let v43 = fields[1];
let v44 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v44 else { return Ok(None); }
;
let v45 = fields[0];
let v46 = fields[1];
let v47 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v47 { return Ok(None); }
let v48 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo__24eo_5fpf, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v36) { Ok(v) => v, Err(e) => return Err(e) };
more_67_eo__24eo_5fcmd_5fstep_5fproven(s, v50, a0, v39, v42, v45, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49)
}
pub(super) fn case_343_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v25 else { return Ok(None); }
;
let v26 = fields[0];
let v27 = fields[1];
let v28 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v28 else { return Ok(None); }
;
let v29 = fields[0];
let v30 = fields[1];
more_66_eo__24eo_5fcmd_5fstep_5fproven(s, v30, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29)
}
pub(super) fn cases_0_85_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_340_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_341_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_342_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_343_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v237: Term, v251: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v252 = match s.apply(v237, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v227, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Binary(BitVec::new(0, &v254))) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v253, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v226, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v203, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v180, v258) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v259))
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v238: Term, a4: Term, a9: Term, a0: Term, a1: Term, v237: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v239 = match s.apply(v238, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.literal(Lit::Numeral(v241)) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_extract, &[a9, v242]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.builtin_list(EvalOp::ListConcat, &[v245, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.builtin_list(EvalOp::ListSingletonElim, &[v244, v246]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v243, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match eo__24eo_5ftypeof(s, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match eo__24eo_5fnil(s, v240, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v239, v250) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v237, v251, v227, v226, v203, v180)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v204: Term, v225: Term, a9: Term, a0: Term, a1: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v226 = match s.apply(v204, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(v229)) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_extract, &[a9, v230]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.builtin_list(EvalOp::ListConcat, &[v233, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.builtin_list(EvalOp::ListSingletonElim, &[v232, v234]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v231, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v228, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v238, a4, a9, a0, a1, v237, v227, v226, v203, v180)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v213: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v212: Term, v204: Term, a9: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v214 = match s.apply(v213, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.builtin_list(EvalOp::ListConcat, &[v218, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.builtin_list(EvalOp::ListSingletonElim, &[v217, v219]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v216, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24eo_5ftypeof(s, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match eo__24eo_5fnil(s, v215, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v214, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v212, v224) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v204, v225, a9, a0, a1, a4, v203, v180)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v189: Term, v201: Term, v181: Term, a7: Term, a8: Term, a0: Term, a1: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
let v202 = match s.apply(v189, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v181, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.builtin_list(EvalOp::ListConcat, &[v208, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_list(EvalOp::ListSingletonElim, &[v207, v209]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v206, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v205, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v213, a2, a7, a8, a0, a1, v212, v204, a9, a4, v203, v180)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v189: Term, v181: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
let v190 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v190, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.builtin_list(EvalOp::ListConcat, &[v195, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_list(EvalOp::ListSingletonElim, &[v194, v196]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v193, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match eo__24eo_5ftypeof(s, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match eo__24eo_5fnil(s, v192, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v191, v200) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v189, v201, v181, a7, a8, a0, a1, a2, a9, a4, v180)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v177: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a3: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term) -> CheckResult<Option<Term>> {
let v178 = match s.apply(v177, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_list(EvalOp::ListConcat, &[v164, a0, v178]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v163, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.builtin_list(EvalOp::ListConcat, &[v185, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.builtin_list(EvalOp::ListSingletonElim, &[v184, v186]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v183, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v182, v188) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v189, v181, a7, a8, a2, a9, a4, v180)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v165 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v166, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.literal(Lit::Binary(BitVec::new(0, &v172))) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v171, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v169, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v167, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v165, v176) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v177, a1, v164, a0, v163, a5, a6, a3, a7, a8, a2, a9, a4)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v145: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v150 = match s.unapply(v145) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v151, v152)) = v150 else { return Ok(None); }
;
let v153 = match s.unapply(v151) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v154, v155)) = v153 else { return Ok(None); }
;
let v156 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v154 != v156 { return Ok(None); }
let v157 = match s.unapply(v155) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v158, v159)) = v157 else { return Ok(None); }
;
let v160 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v158 != v160 { return Ok(None); }
if v159 != a4 { return Ok(None); }
let v161 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.literal(Lit::Numeral(v161)) { Ok(v) => v, Err(e) => return Err(e) };
if v152 != v162 { return Ok(None); }
let v163 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a3, a2, a4, a1, v164, a0, v163, a5, a6, a7, a8, a9)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v134: Term, v136: Term, v135: Term, a8: Term, v132: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v134 != v136 { return Ok(None); }
if v135 != a8 { return Ok(None); }
let v137 = match s.unapply(v132) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v138, v139)) = v137 else { return Ok(None); }
;
let v140 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v138 != v140 { return Ok(None); }
if v139 != a4 { return Ok(None); }
let v141 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v141 else { return Ok(None); }
;
let v142 = fields[0];
let v143 = match s.unapply(v142) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v144, v145)) = v143 else { return Ok(None); }
;
let v146 = match s.unapply(v144) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v147, v148)) = v146 else { return Ok(None); }
;
let v149 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v147 != v149 { return Ok(None); }
if v148 != a9 { return Ok(None); }
more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v145, a4, a3, a2, a1, a0, a5, a6, a7, a8, a9)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v118: Term, a4: Term, v115: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v120 = match s.unapply(v118) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v121, v122)) = v120 else { return Ok(None); }
;
let v123 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v121 != v123 { return Ok(None); }
if v122 != a4 { return Ok(None); }
let v124 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(v124)) { Ok(v) => v, Err(e) => return Err(e) };
if v115 != v125 { return Ok(None); }
let v126 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(v126)) { Ok(v) => v, Err(e) => return Err(e) };
if v97 != v127 { return Ok(None); }
let v128 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v128 else { return Ok(None); }
;
let v129 = fields[0];
let v130 = match s.unapply(v129) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v131, v132)) = v130 else { return Ok(None); }
;
let v133 = match s.unapply(v131) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v134, v135)) = v133 else { return Ok(None); }
;
let v136 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v134, v136, v135, a8, v132, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v100: Term, a2: Term, a4: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.unapply(v103) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v106, v107)) = v105 else { return Ok(None); }
;
let v108 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v106 != v108 { return Ok(None); }
let v109 = match s.unapply(v107) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v110, v111)) = v109 else { return Ok(None); }
;
let v112 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v110 != v112 { return Ok(None); }
if v111 != a2 { return Ok(None); }
let v113 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.unapply(v114) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v117, v118)) = v116 else { return Ok(None); }
;
let v119 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v117 != v119 { return Ok(None); }
more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v118, a4, v115, v97, a13, a8, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v75: Term, a12: Term, a7: Term, a2: Term, a4: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v84 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Numeral(v84)) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v85 { return Ok(None); }
let v86 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v86 else { return Ok(None); }
;
let v87 = fields[0];
let v88 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v92, v93)) = v91 else { return Ok(None); }
;
let v94 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v92 != v94 { return Ok(None); }
if v93 != a7 { return Ok(None); }
let v95 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.unapply(v96) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v99, v100)) = v98 else { return Ok(None); }
;
let v101 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v99 != v101 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v100, a2, a4, v97, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v67: Term, a2: Term, v64: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
if v71 != a2 { return Ok(None); }
let v73 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v77 != v79 { return Ok(None); }
let v80 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v81 != v83 { return Ok(None); }
if v82 != a4 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v75, a12, a7, a2, a4, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v11: Term, a11: Term, a6: Term, a2: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v51 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(v51)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v52 { return Ok(None); }
let v53 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v53 else { return Ok(None); }
;
let v54 = fields[0];
let v55 = match s.unapply(v54) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a6 { return Ok(None); }
let v62 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v66 != v68 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v67, a2, v64, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v35: Term, v37: Term, v36: Term, a2: Term, v29: Term, a3: Term, v11: Term, a11: Term, a6: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
if v35 != v37 { return Ok(None); }
if v36 != a2 { return Ok(None); }
let v38 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != a3 { return Ok(None); }
let v49 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Numeral(v49)) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v50 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v11, a11, a6, a2, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v20: Term, v21: Term, a4: Term, v18: Term, a2: Term, a3: Term, v11: Term, a11: Term, a6: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a4 { return Ok(None); }
let v27 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v35, v37, v36, a2, v29, a3, v11, a11, a6, a4, a12, a7, a13, a8, a14, a9, a1, a0, a5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a5 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v20, v21, a4, v18, a2, a3, v11, a11, a6, a12, a7, a13, a8, a14, a9, a1, a0, a5)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
let stuck8 = match s.is_stuck(a8) { Ok(v) => v, Err(e) => return Err(e) };
if stuck8 { return Ok(s.stuck()); }
let stuck9 = match s.is_stuck(a9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck9 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-or-concat-pullup3"
pub fn eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
s.leave();
result
}
pub(super) fn more_69_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v50: Term, a0: Term, v39: Term, v42: Term, v45: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term, v49: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo__24eo_5fpf, &[v50]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo__24eo_5fpf, &[v52]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__24eo_5fpf, &[v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__24eo_5fpf, &[v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49, v51, v53, v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn more_68_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v30: Term, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v31 { return Ok(None); }
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v35 else { return Ok(None); }
;
let v36 = fields[0];
let v37 = fields[1];
let v38 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
let v40 = fields[1];
let v41 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v41 else { return Ok(None); }
;
let v42 = fields[0];
let v43 = fields[1];
let v44 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v44 else { return Ok(None); }
;
let v45 = fields[0];
let v46 = fields[1];
let v47 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v47 { return Ok(None); }
let v48 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo__24eo_5fpf, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v36) { Ok(v) => v, Err(e) => return Err(e) };
more_69_eo__24eo_5fcmd_5fstep_5fproven(s, v50, a0, v39, v42, v45, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49)
}
pub(super) fn case_344_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v25 else { return Ok(None); }
;
let v26 = fields[0];
let v27 = fields[1];
let v28 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v28 else { return Ok(None); }
;
let v29 = fields[0];
let v30 = fields[1];
more_68_eo__24eo_5fcmd_5fstep_5fproven(s, v30, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v237: Term, v251: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v252 = match s.apply(v237, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v227, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Binary(BitVec::new(0, &v254))) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v253, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v226, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v203, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v180, v258) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v259))
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v238: Term, a4: Term, a9: Term, a0: Term, a1: Term, v237: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v239 = match s.apply(v238, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.literal(Lit::Numeral(v241)) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_extract, &[a9, v242]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.builtin_list(EvalOp::ListConcat, &[v245, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.builtin_list(EvalOp::ListSingletonElim, &[v244, v246]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v243, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match eo__24eo_5ftypeof(s, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match eo__24eo_5fnil(s, v240, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v239, v250) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v237, v251, v227, v226, v203, v180)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v204: Term, v225: Term, a9: Term, a0: Term, a1: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v226 = match s.apply(v204, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(v229)) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_extract, &[a9, v230]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.builtin_list(EvalOp::ListConcat, &[v233, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.builtin_list(EvalOp::ListSingletonElim, &[v232, v234]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v231, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v228, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v238, a4, a9, a0, a1, v237, v227, v226, v203, v180)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v213: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v212: Term, v204: Term, a9: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
let v214 = match s.apply(v213, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.builtin_list(EvalOp::ListConcat, &[v218, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.builtin_list(EvalOp::ListSingletonElim, &[v217, v219]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v216, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24eo_5ftypeof(s, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match eo__24eo_5fnil(s, v215, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v214, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v212, v224) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v204, v225, a9, a0, a1, a4, v203, v180)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v189: Term, v201: Term, v181: Term, a7: Term, a8: Term, a0: Term, a1: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
let v202 = match s.apply(v189, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v181, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.builtin_list(EvalOp::ListConcat, &[v208, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_list(EvalOp::ListSingletonElim, &[v207, v209]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v206, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v205, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v213, a2, a7, a8, a0, a1, v212, v204, a9, a4, v203, v180)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v189: Term, v181: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
let v190 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v190, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.builtin_list(EvalOp::ListConcat, &[v195, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_list(EvalOp::ListSingletonElim, &[v194, v196]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v193, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match eo__24eo_5ftypeof(s, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match eo__24eo_5fnil(s, v192, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v191, v200) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v189, v201, v181, a7, a8, a0, a1, a2, a9, a4, v180)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v177: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a3: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term) -> CheckResult<Option<Term>> {
let v178 = match s.apply(v177, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_list(EvalOp::ListConcat, &[v164, a0, v178]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v163, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.builtin_list(EvalOp::ListConcat, &[v185, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.builtin_list(EvalOp::ListSingletonElim, &[v184, v186]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v183, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v182, v188) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v189, v181, a7, a8, a2, a9, a4, v180)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v165 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v166, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.literal(Lit::Binary(BitVec::new(0, &v172))) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v171, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v169, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v167, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v165, v176) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v177, a1, v164, a0, v163, a5, a6, a3, a7, a8, a2, a9, a4)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v145: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v150 = match s.unapply(v145) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v151, v152)) = v150 else { return Ok(None); }
;
let v153 = match s.unapply(v151) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v154, v155)) = v153 else { return Ok(None); }
;
let v156 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v154 != v156 { return Ok(None); }
let v157 = match s.unapply(v155) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v158, v159)) = v157 else { return Ok(None); }
;
let v160 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v158 != v160 { return Ok(None); }
if v159 != a4 { return Ok(None); }
let v161 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.literal(Lit::Numeral(v161)) { Ok(v) => v, Err(e) => return Err(e) };
if v152 != v162 { return Ok(None); }
let v163 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a3, a2, a4, a1, v164, a0, v163, a5, a6, a7, a8, a9)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v134: Term, v136: Term, v135: Term, a8: Term, v132: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v134 != v136 { return Ok(None); }
if v135 != a8 { return Ok(None); }
let v137 = match s.unapply(v132) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v138, v139)) = v137 else { return Ok(None); }
;
let v140 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v138 != v140 { return Ok(None); }
if v139 != a4 { return Ok(None); }
let v141 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v141 else { return Ok(None); }
;
let v142 = fields[0];
let v143 = match s.unapply(v142) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v144, v145)) = v143 else { return Ok(None); }
;
let v146 = match s.unapply(v144) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v147, v148)) = v146 else { return Ok(None); }
;
let v149 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v147 != v149 { return Ok(None); }
if v148 != a9 { return Ok(None); }
more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v145, a4, a3, a2, a1, a0, a5, a6, a7, a8, a9)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v118: Term, a4: Term, v115: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v120 = match s.unapply(v118) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v121, v122)) = v120 else { return Ok(None); }
;
let v123 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v121 != v123 { return Ok(None); }
if v122 != a4 { return Ok(None); }
let v124 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(v124)) { Ok(v) => v, Err(e) => return Err(e) };
if v115 != v125 { return Ok(None); }
let v126 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(v126)) { Ok(v) => v, Err(e) => return Err(e) };
if v97 != v127 { return Ok(None); }
let v128 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v128 else { return Ok(None); }
;
let v129 = fields[0];
let v130 = match s.unapply(v129) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v131, v132)) = v130 else { return Ok(None); }
;
let v133 = match s.unapply(v131) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v134, v135)) = v133 else { return Ok(None); }
;
let v136 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v134, v136, v135, a8, v132, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v100: Term, a2: Term, a4: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.unapply(v103) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v106, v107)) = v105 else { return Ok(None); }
;
let v108 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v106 != v108 { return Ok(None); }
let v109 = match s.unapply(v107) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v110, v111)) = v109 else { return Ok(None); }
;
let v112 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v110 != v112 { return Ok(None); }
if v111 != a2 { return Ok(None); }
let v113 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.unapply(v114) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v117, v118)) = v116 else { return Ok(None); }
;
let v119 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v117 != v119 { return Ok(None); }
more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v118, a4, v115, v97, a13, a8, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v75: Term, a12: Term, a7: Term, a2: Term, a4: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v84 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Numeral(v84)) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v85 { return Ok(None); }
let v86 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v86 else { return Ok(None); }
;
let v87 = fields[0];
let v88 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v92, v93)) = v91 else { return Ok(None); }
;
let v94 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v92 != v94 { return Ok(None); }
if v93 != a7 { return Ok(None); }
let v95 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.unapply(v96) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v99, v100)) = v98 else { return Ok(None); }
;
let v101 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v99 != v101 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v100, a2, a4, v97, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v67: Term, a2: Term, v64: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
if v71 != a2 { return Ok(None); }
let v73 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v77 != v79 { return Ok(None); }
let v80 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v81 != v83 { return Ok(None); }
if v82 != a4 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v75, a12, a7, a2, a4, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v11: Term, a11: Term, a6: Term, a2: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v51 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(v51)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v52 { return Ok(None); }
let v53 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v53 else { return Ok(None); }
;
let v54 = fields[0];
let v55 = match s.unapply(v54) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a6 { return Ok(None); }
let v62 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v66 != v68 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v67, a2, v64, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v35: Term, v37: Term, v36: Term, a2: Term, v29: Term, a3: Term, v11: Term, a11: Term, a6: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
if v35 != v37 { return Ok(None); }
if v36 != a2 { return Ok(None); }
let v38 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != a3 { return Ok(None); }
let v49 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Numeral(v49)) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v50 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v11, a11, a6, a2, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v20: Term, v21: Term, a4: Term, v18: Term, a2: Term, a3: Term, v11: Term, a11: Term, a6: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a4 { return Ok(None); }
let v27 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v35, v37, v36, a2, v29, a3, v11, a11, a6, a4, a12, a7, a13, a8, a14, a9, a1, a0, a5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a5 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v20, v21, a4, v18, a2, a3, v11, a11, a6, a12, a7, a13, a8, a14, a9, a1, a0, a5)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Term> {
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
let stuck7 = match s.is_stuck(a7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck7 { return Ok(s.stuck()); }
let stuck8 = match s.is_stuck(a8) { Ok(v) => v, Err(e) => return Err(e) };
if stuck8 { return Ok(s.stuck()); }
let stuck9 = match s.is_stuck(a9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck9 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-concat-pullup3"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
s.leave();
result
}
pub(super) fn more_71_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v50: Term, a0: Term, v39: Term, v42: Term, v45: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term, v49: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo__24eo_5fpf, &[v50]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo__24eo_5fpf, &[v52]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__24eo_5fpf, &[v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__24eo_5fpf, &[v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49, v51, v53, v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn more_70_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v30: Term, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v31 { return Ok(None); }
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v35 else { return Ok(None); }
;
let v36 = fields[0];
let v37 = fields[1];
let v38 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
let v40 = fields[1];
let v41 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v41 else { return Ok(None); }
;
let v42 = fields[0];
let v43 = fields[1];
let v44 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v44 else { return Ok(None); }
;
let v45 = fields[0];
let v46 = fields[1];
let v47 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v47 { return Ok(None); }
let v48 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo__24eo_5fpf, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v36) { Ok(v) => v, Err(e) => return Err(e) };
more_71_eo__24eo_5fcmd_5fstep_5fproven(s, v50, a0, v39, v42, v45, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49)
}
pub(super) fn case_345_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v16 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v16 else { return Ok(None); }
;
let v17 = fields[0];
let v18 = fields[1];
let v19 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v19 else { return Ok(None); }
;
let v20 = fields[0];
let v21 = fields[1];
let v22 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v22 else { return Ok(None); }
;
let v23 = fields[0];
let v24 = fields[1];
let v25 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v25 else { return Ok(None); }
;
let v26 = fields[0];
let v27 = fields[1];
let v28 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v28 else { return Ok(None); }
;
let v29 = fields[0];
let v30 = fields[1];
more_70_eo__24eo_5fcmd_5fstep_5fproven(s, v30, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s: &mut Store, v23: Term, v27: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v23, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s: &mut Store, v14: Term, a0: Term, v13: Term, a1: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fnil(s, v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v15, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s, v23, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a1 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s, v14, a0, v13, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-duplicate"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_346_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fduplicate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, v22: Term, v29: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v22, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListConcat, &[v33, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_list(EvalOp::ListSingletonElim, &[v32, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v31, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v30, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, v17: Term, v19: Term, v18: Term, a3: Term, v11: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a3 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListConcat, &[v23, a0, v28]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dxor_2dones(s, v22, v29, a0, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxor_2dones(s, v17, v19, v18, a3, v11, a2, a1, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dones(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-ones"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dones(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_72_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fbv_2dxor_2dones(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_347_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fones, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v13 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v17 { return Ok(None); }
let v18 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_72_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_86_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_344_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_345_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_346_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_347_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dnot(s: &mut Store, v20: Term, v23: Term, v18: Term, v16: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v18, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dnot(s: &mut Store, v11: Term, v9: Term, v8: Term, v4: Term, v0: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match eo__24eo_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fnil(s, v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v4, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fnil(s, v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dxor_2dnot(s, v20, v23, v18, v16)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dnot(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxor_2dnot(s, v11, v9, v8, v4, v0, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dnot(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dnot(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-not"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dnot(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dnot(s, a0, a1);
s.leave();
result
}
pub(super) fn case_348_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dxor_2dnot(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dnot_2didemp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dnot_2didemp(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dnot_2didemp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-not-idemp"
pub fn eo__24eo_5fprog_5fbv_2dnot_2didemp(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dnot_2didemp(s, a0);
s.leave();
result
}
pub(super) fn case_349_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fnot_5fidemp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dnot_2didemp(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s: &mut Store, v12: Term, v11: Term, v9: Term, v8: Term) -> CheckResult<Option<Term>> {
let v13 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v8, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s, v12, v11, v9, v8)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ult-zero-1"
pub fn eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s, a0, a1);
s.leave();
result
}
pub(super) fn case_350_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fult_5fzero_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dult_2dzero_2d2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ult-zero-2"
pub fn eo__24eo_5fprog_5fbv_2dult_2dzero_2d2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dult_2dzero_2d2(s, a0, a1);
s.leave();
result
}
pub(super) fn case_351_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fult_5fzero_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dult_2dzero_2d2(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_87_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_348_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_349_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_350_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_351_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_21_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_84_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_85_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_86_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_87_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2dself(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dult_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dult_2dself(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ult-self"
pub fn eo__24eo_5fprog_5fbv_2dult_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dult_2dself(s, a0);
s.leave();
result
}
pub(super) fn case_352_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fult_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dult_2dself(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dlt_2dself(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dlt_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dlt_2dself(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-lt-self"
pub fn eo__24eo_5fprog_5fbv_2dlt_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dlt_2dself(s, a0);
s.leave();
result
}
pub(super) fn case_353_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5flt_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dlt_2dself(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dule_2dself(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dule_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dule_2dself(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ule-self"
pub fn eo__24eo_5fprog_5fbv_2dule_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dule_2dself(s, a0);
s.leave();
result
}
pub(super) fn case_354_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fule_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dule_2dself(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dule_2dzero(s: &mut Store, v11: Term, v13: Term, v10: Term, v8: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v8, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dule_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(v12)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dule_2dzero(s, v11, v13, v10, v8)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dule_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dule_2dzero(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ule-zero"
pub fn eo__24eo_5fprog_5fbv_2dule_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dule_2dzero(s, a0, a1);
s.leave();
result
}
pub(super) fn case_355_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fule_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dule_2dzero(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_88_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_352_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_353_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_354_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_355_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dule(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dzero_2dule(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dzero_2dule(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-zero-ule"
pub fn eo__24eo_5fprog_5fbv_2dzero_2dule(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dzero_2dule(s, a0, a1);
s.leave();
result
}
pub(super) fn case_356_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fzero_5fule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dzero_2dule(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsle_2dself(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvsle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsle_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsle_2dself(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sle-self"
pub fn eo__24eo_5fprog_5fbv_2dsle_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsle_2dself(s, a0);
s.leave();
result
}
pub(super) fn case_357_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsle_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dsle_2dself(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, v45: Term) -> CheckResult<Option<Term>> {
let v46 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, v34: Term, v35: Term, a0: Term, v24: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a0 { return Ok(None); }
let v37 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v38 { return Ok(None); }
let v39 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v39, v44) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dule_2dmax(s, v45)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, v16: Term, a1: Term, v17: Term, a0: Term, a2: Term) -> CheckResult<Option<Term>> {
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != a1 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
let v29 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v32 { return Ok(None); }
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dule_2dmax(s, v34, v35, a0, v24, a2, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a2 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dule_2dmax(s, v16, a1, v17, a0, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dule_2dmax(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ule-max"
pub fn eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dule_2dmax(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_73_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fbv_2dule_2dmax(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_358_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fule_5fmax, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = fields[1];
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v17 { return Ok(None); }
let v18 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_73_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dnot_2dult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dnot_2dult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dnot_2dult(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-not-ult"
pub fn eo__24eo_5fprog_5fbv_2dnot_2dult(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dnot_2dult(s, a0, a1);
s.leave();
result
}
pub(super) fn case_359_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fnot_5fult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dnot_2dult(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_89_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_356_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_357_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_358_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_359_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v86: Term, v88: Term, v80: Term, v67: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v86, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v80, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v67, v90) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v91))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v74: Term, a2: Term, a1: Term, v73: Term, a0: Term, v72: Term, v71: Term, v68: Term, a5: Term, v67: Term) -> CheckResult<Option<Term>> {
let v75 = match s.apply(v74, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.builtin_list(EvalOp::ListConcat, &[v73, a0, v76]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_list(EvalOp::ListSingletonElim, &[v72, v77]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v71, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v68, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(v83)) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v82, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v81, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Binary(BitVec::new(0, &v87))) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v86, v88, v80, v67)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v61: Term, a4: Term, v60: Term, a1: Term, v59: Term, v57: Term, a0: Term, v56: Term, a6: Term, a2: Term, a5: Term) -> CheckResult<Option<Term>> {
let v62 = match s.apply(v61, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v60, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v59, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_list(EvalOp::ListConcat, &[v57, a0, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v56, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(v69)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_extract, &[a6, v70]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v74, a2, a1, v73, a0, v72, v71, v68, a5, v67)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v45: Term, a4: Term, v38: Term, a2: Term, a3: Term, a1: Term, a0: Term, a6: Term, a5: Term) -> CheckResult<Option<Term>> {
let v50 = match s.unapply(v45) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v53 { return Ok(None); }
if v52 != a4 { return Ok(None); }
let v54 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(v54)) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v55 { return Ok(None); }
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v61, a4, v60, a1, v59, v57, a0, v56, a6, a2, a5)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v33: Term, v34: Term, a6: Term, v31: Term, a3: Term, a4: Term, a2: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v35 { return Ok(None); }
if v34 != a6 { return Ok(None); }
let v36 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v40, v41)) = v39 else { return Ok(None); }
;
let v42 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v42 { return Ok(None); }
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v47 != v49 { return Ok(None); }
if v48 != a3 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v45, a4, v38, a2, a3, a1, a0, a6, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v15: Term, a5: Term, a4: Term, a9: Term, a6: Term, a3: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v16 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a5 { return Ok(None); }
let v23 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a4 { return Ok(None); }
let v27 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v27 else { return Ok(None); }
;
let v28 = fields[0];
let v29 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v33, v34)) = v32 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v33, v34, a6, v31, a3, a4, a2, a1, a0, a5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a4 { return Ok(None); }
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v15, a5, a4, a9, a6, a3, a2, a1, a0)
}
