//! Generated functions, module 7 of 12.
#[allow(unused_imports)]
use super::*;
use crate::*;
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
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v0, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
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
pub(super) fn cases_39_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_312_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_313_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_314_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_315_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_316_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_317_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_318_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_319_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
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
let v16 = match s.apply(v9, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v0, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
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
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
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
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
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
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, v24: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v9, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
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
more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s, v24, a2, v9)
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
pub(super) fn cases_40_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_320_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_321_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_322_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_323_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v61: Term, v63: Term, v59: Term, a3: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v78 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Binary(BitVec::new(0, &v78))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v77, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v71, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v65, v81) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v82))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v61, v63, v59, a3, a0, a1)
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v34, v35, a0, v32, a1, a2, a3)
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
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, a2: Term, a1: Term, v61: Term, v59: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a1: Term, v32: Term, a0: Term, v25: Term, a6: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v45 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
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
more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, a2, a1, v61, v59, a3)
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2(s, v34, v36, v35, a1, v32, a0, v25, a6, a3, a2)
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v59: Term, v55: Term, v49: Term) -> CheckResult<Option<Term>> {
let v60 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.literal(Lit::Binary(BitVec::new(0, &v60))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v55, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v49, v63) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v64))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v59, v55, v49)
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v34, v35, a0, v32, a2, a1, a3)
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
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a1: Term, v32: Term, a0: Term, v25: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v45 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v45 { return Ok(None); }
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, v34, v36, v35, a1, v32, a0, v25, a2)
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
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v56: Term, v58: Term, v55: Term, v49: Term) -> CheckResult<Option<Term>> {
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.literal(Lit::Binary(BitVec::new(0, &v60))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v55, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v49, v63) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v64))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v56, v58, v55, v49)
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v34, v35, a0, v32, a2, a1, a3)
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
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn cases_41_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_328_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_329_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_330_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_331_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_332_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_333_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_334_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_335_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v87: Term, v91: Term) -> CheckResult<Option<Term>> {
let v92 = match s.apply(v87, v91) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v92))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v64: Term, a0: Term, v57: Term, a8: Term, a4: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v87, v91)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a1: Term, v32: Term, a0: Term, v25: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v45 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
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
more_1_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v64, a0, v57, a8, a4, a2, a1, a3)
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_0_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v34, v36, v35, a1, v32, a0, v25, a7, a3, a8, a4, a2)
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
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v133: Term, v142: Term, v132: Term, v130: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v107: Term, v116: Term, v96: Term, v88: Term, a7: Term, a0: Term, a1: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v133, v142, v132, v130, v120, v119, v87)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v91: Term, v90: Term, v89: Term, a3: Term, a4: Term, a5: Term, a6: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v107, v116, v96, v88, a7, a0, a1, a2, v87)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v66: Term, v68: Term, v67: Term, a2: Term, v60: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, a0, a1, v91, v90, v89, a3, a4, a5, a6, v88, a7, a2, v87)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v34: Term, a3: Term, v35: Term, a2: Term, a4: Term, v24: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v66, v68, v67, a2, v60, a3, a4, a1, a0, a5, a6, a7)
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
more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v34, a3, v35, a2, a4, v24, a10, a7, a1, a0, a5, a6)
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
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v133: Term, v142: Term, v132: Term, v130: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v107: Term, v116: Term, v96: Term, v88: Term, a7: Term, a0: Term, a1: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v133, v142, v132, v130, v120, v119, v87)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v91: Term, v90: Term, v89: Term, a3: Term, a4: Term, a5: Term, a6: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v107, v116, v96, v88, a7, a0, a1, a2, v87)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v66: Term, v68: Term, v67: Term, a2: Term, v60: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, a0, a1, v91, v90, v89, a3, a4, a5, a6, v88, a7, a2, v87)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v34: Term, a3: Term, v35: Term, a2: Term, a4: Term, v24: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v66, v68, v67, a2, v60, a3, a4, a1, a0, a5, a6, a7)
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
more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v34, a3, v35, a2, a4, v24, a10, a7, a1, a0, a5, a6)
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
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v133: Term, v142: Term, v132: Term, v130: Term, v120: Term, v119: Term, v87: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v107: Term, v116: Term, v96: Term, v88: Term, a7: Term, a0: Term, a1: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v133, v142, v132, v130, v120, v119, v87)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v91: Term, v90: Term, v89: Term, a3: Term, a4: Term, a5: Term, a6: Term, v88: Term, a7: Term, a2: Term, v87: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v107, v116, v96, v88, a7, a0, a1, a2, v87)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v66: Term, v68: Term, v67: Term, a2: Term, v60: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, a0, a1, v91, v90, v89, a3, a4, a5, a6, v88, a7, a2, v87)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v34: Term, a3: Term, v35: Term, a2: Term, a4: Term, v24: Term, a10: Term, a7: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v66, v68, v67, a2, v60, a3, a4, a1, a0, a5, a6, a7)
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
more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v34, a3, v35, a2, a4, v24, a10, a7, a1, a0, a5, a6)
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
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v178: Term, v175: Term, v174: Term, v167: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
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
let v192 = match s.apply(v156, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v133, v192) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v193))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v145: Term, v152: Term, v144: Term, v142: Term, v134: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, a0, a1, v178, v175, v174, v167, v157, v156, v133)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v125: Term, v128: Term, v123: Term, a1: Term, v122: Term, a0: Term, v121: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v145, v152, v144, v142, v134, a7, a0, a1, a2, a4, v133)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v102: Term, a3: Term, v103: Term, a2: Term, a4: Term, v92: Term, v85: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v125, v128, v123, a1, v122, a0, v121, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v102, a3, v103, a2, a4, v92, v85, a1, a0, a5, a6, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v11: Term, a3: Term, a9: Term, a5: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v69, v70, a2, v67, a4, v49, a10, a7, a3, a1, a0, a5, a6)
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
more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v11, a3, a9, a5, a2, a4, a10, a7, a1, a0, a6)
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
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v178: Term, v175: Term, v174: Term, v167: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
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
let v192 = match s.apply(v156, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v133, v192) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v193))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v145: Term, v152: Term, v144: Term, v142: Term, v134: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, a0, a1, v178, v175, v174, v167, v157, v156, v133)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v125: Term, v128: Term, v123: Term, a1: Term, v122: Term, a0: Term, v121: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v145, v152, v144, v142, v134, a7, a0, a1, a2, a4, v133)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v102: Term, a3: Term, v103: Term, a2: Term, a4: Term, v92: Term, v85: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v125, v128, v123, a1, v122, a0, v121, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v102, a3, v103, a2, a4, v92, v85, a1, a0, a5, a6, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v11: Term, a3: Term, a9: Term, a5: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v69, v70, a2, v67, a4, v49, a10, a7, a3, a1, a0, a5, a6)
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
more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v11, a3, a9, a5, a2, a4, a10, a7, a1, a0, a6)
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
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v178: Term, v175: Term, v174: Term, v167: Term, v157: Term, v156: Term, v133: Term) -> CheckResult<Option<Term>> {
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
let v192 = match s.apply(v156, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v133, v192) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v193))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v145: Term, v152: Term, v144: Term, v142: Term, v134: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v133: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, a0, a1, v178, v175, v174, v167, v157, v156, v133)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v125: Term, v128: Term, v123: Term, a1: Term, v122: Term, a0: Term, v121: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v145, v152, v144, v142, v134, a7, a0, a1, a2, a4, v133)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v102: Term, a3: Term, v103: Term, a2: Term, a4: Term, v92: Term, v85: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v125, v128, v123, a1, v122, a0, v121, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v102, a3, v103, a2, a4, v92, v85, a1, a0, a5, a6, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v11: Term, a3: Term, a9: Term, a5: Term, a2: Term, a4: Term, a10: Term, a7: Term, a1: Term, a0: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v69, v70, a2, v67, a4, v49, a10, a7, a3, a1, a0, a5, a6)
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
more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v11, a3, a9, a5, a2, a4, a10, a7, a1, a0, a6)
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
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v238: Term, a4: Term, a9: Term, a0: Term, a1: Term, v237: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v213: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v212: Term, v204: Term, a9: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
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
more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v238, a4, a9, a0, a1, v237, v227, v226, v203, v180)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v189: Term, v181: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
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
more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v213, a2, a7, a8, a0, a1, v212, v204, a9, a4, v203, v180)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v189, v181, a7, a8, a2, a9, a4, v180)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v134: Term, v136: Term, v135: Term, a8: Term, v132: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a3, a2, a4, a1, v164, a0, v163, a5, a6, a7, a8, a9)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v100: Term, a2: Term, a4: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v134, v136, v135, a8, v132, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v67: Term, a2: Term, v64: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v100, a2, a4, v97, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v35: Term, v37: Term, v36: Term, a2: Term, v29: Term, a3: Term, v11: Term, a11: Term, a6: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v67, a2, v64, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
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
more_0_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v35, v37, v36, a2, v29, a3, v11, a11, a6, a4, a12, a7, a13, a8, a14, a9, a1, a0, a5)
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
pub(super) fn more_5_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v50: Term, a0: Term, v39: Term, v42: Term, v45: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term, v49: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fcmd_5fstep_5fproven(s, v50, a0, v39, v42, v45, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49)
}
pub(super) fn cases_42_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_336_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_337_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_338_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_339_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_340_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_341_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_342_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_343_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v238: Term, a4: Term, a9: Term, a0: Term, a1: Term, v237: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v213: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v212: Term, v204: Term, a9: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
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
more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v238, a4, a9, a0, a1, v237, v227, v226, v203, v180)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v189: Term, v181: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
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
more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v213, a2, a7, a8, a0, a1, v212, v204, a9, a4, v203, v180)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v189, v181, a7, a8, a2, a9, a4, v180)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v134: Term, v136: Term, v135: Term, a8: Term, v132: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a3, a2, a4, a1, v164, a0, v163, a5, a6, a7, a8, a9)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v100: Term, a2: Term, a4: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v134, v136, v135, a8, v132, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v67: Term, a2: Term, v64: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v100, a2, a4, v97, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v35: Term, v37: Term, v36: Term, a2: Term, v29: Term, a3: Term, v11: Term, a11: Term, a6: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v67, a2, v64, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
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
more_0_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v35, v37, v36, a2, v29, a3, v11, a11, a6, a4, a12, a7, a13, a8, a14, a9, a1, a0, a5)
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
pub(super) fn more_6_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v50: Term, a0: Term, v39: Term, v42: Term, v45: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term, v49: Term) -> CheckResult<Option<Term>> {
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
more_6_eo__24eo_5fcmd_5fstep_5fproven(s, v50, a0, v39, v42, v45, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v238: Term, a4: Term, a9: Term, a0: Term, a1: Term, v237: Term, v227: Term, v226: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v213: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v212: Term, v204: Term, a9: Term, a4: Term, v203: Term, v180: Term) -> CheckResult<Option<Term>> {
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
more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v238, a4, a9, a0, a1, v237, v227, v226, v203, v180)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v189: Term, v181: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v180: Term) -> CheckResult<Option<Term>> {
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
more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v213, a2, a7, a8, a0, a1, v212, v204, a9, a4, v203, v180)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v164: Term, a0: Term, v163: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v189, v181, a7, a8, a2, a9, a4, v180)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v134: Term, v136: Term, v135: Term, a8: Term, v132: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a3, a2, a4, a1, v164, a0, v163, a5, a6, a7, a8, a9)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v100: Term, a2: Term, a4: Term, v97: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v134, v136, v135, a8, v132, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v67: Term, a2: Term, v64: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v100, a2, a4, v97, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v35: Term, v37: Term, v36: Term, a2: Term, v29: Term, a3: Term, v11: Term, a11: Term, a6: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v67, a2, v64, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
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
more_0_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v35, v37, v36, a2, v29, a3, v11, a11, a6, a4, a12, a7, a13, a8, a14, a9, a1, a0, a5)
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
pub(super) fn more_7_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v50: Term, a0: Term, v39: Term, v42: Term, v45: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v29: Term, v49: Term) -> CheckResult<Option<Term>> {
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
more_7_eo__24eo_5fcmd_5fstep_5fproven(s, v50, a0, v39, v42, v45, v2, v5, v8, v11, v14, v17, v20, v23, v26, v29, v49)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s: &mut Store, v23: Term, v27: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v23, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
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
more_0_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s, v23, v27)
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, v22: Term, v29: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fbv_2dxor_2dones(s, v22, v29, a0, a1)
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
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fbv_2dxor_2dones(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dnot(s: &mut Store, v20: Term, v23: Term, v18: Term, v16: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v18, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
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
more_0_eo__24eo_5fprog_5fbv_2dxor_2dnot(s, v20, v23, v18, v16)
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
let v13 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v8, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
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
let v9 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
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
pub(super) fn cases_43_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_344_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_345_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_346_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_347_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_348_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_349_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_350_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_351_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2dself(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v5 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v5 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v8, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
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
let v9 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
let v5 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, v34: Term, v35: Term, a0: Term, v24: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v46 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
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
more_0_eo__24eo_5fprog_5fbv_2dule_2dmax(s, v34, v35, a0, v24, a2, a1)
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
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fbv_2dule_2dmax(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
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
pub(super) fn cases_44_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_352_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_353_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_354_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_355_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_356_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_357_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_358_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_359_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v86: Term, v88: Term, v80: Term, v67: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v86, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v80, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v67, v90) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v91))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v61: Term, a4: Term, v60: Term, a1: Term, v59: Term, v57: Term, a0: Term, v56: Term, a6: Term, a2: Term, a5: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v86, v88, v80, v67)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v33: Term, v34: Term, a6: Term, v31: Term, a3: Term, a4: Term, a2: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v61, a4, v60, a1, v59, v57, a0, v56, a6, a2, a5)
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
let v13 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
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
more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v33, v34, a6, v31, a3, a4, a2, a1, a0, a5)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-mult-pow2-1"
pub fn eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9);
s.leave();
result
}
pub(super) fn case_360_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v22 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v22 { return Ok(None); }
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v32 { return Ok(None); }
let v33 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__24eo_5fpf, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__24eo_5fpf, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__24eo_5fpf, &[v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v2, v5, v8, v11, v14, v17, v20, v34, v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v116: Term, v120: Term, v115: Term, v100: Term) -> CheckResult<Option<Term>> {
let v121 = match s.apply(v116, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Binary(BitVec::new(0, &v122))) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v121, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v115, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v100, v125) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v126))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v94: Term, a4: Term, v93: Term, a1: Term, v92: Term, v90: Term, a0: Term, v89: Term, a6: Term, a2: Term, a5: Term) -> CheckResult<Option<Term>> {
let v95 = match s.apply(v94, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v93, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v92, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.builtin_list(EvalOp::ListConcat, &[v90, a0, v98]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v89, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_extract, &[a6, v103]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.builtin_list(EvalOp::ListConcat, &[v107, a0, v110]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_list(EvalOp::ListSingletonElim, &[v106, v111]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v105, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v104, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v101, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.literal(Lit::Numeral(v118)) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v117, v119) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v116, v120, v115, v100)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v66: Term, a3: Term, v67: Term, a4: Term, v60: Term, a2: Term, a1: Term, a0: Term, a6: Term, a5: Term) -> CheckResult<Option<Term>> {
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a3 { return Ok(None); }
let v72 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
let v75 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v75 { return Ok(None); }
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v80, v81)) = v79 else { return Ok(None); }
;
let v82 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v80 != v82 { return Ok(None); }
let v83 = match s.unapply(v81) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v86 { return Ok(None); }
if v85 != a3 { return Ok(None); }
if v78 != a4 { return Ok(None); }
let v87 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(v87)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v88 { return Ok(None); }
let v89 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v94, a4, v93, a1, v92, v90, a0, v89, a6, a2, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v32: Term, a5: Term, v29: Term, a3: Term, a4: Term, a9: Term, a6: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
if v32 != a5 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != a3 { return Ok(None); }
if v40 != a4 { return Ok(None); }
let v49 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
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
if v56 != a6 { return Ok(None); }
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
more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v66, a3, v67, a4, v60, a2, a1, a0, a6, a5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a3 { return Ok(None); }
if v15 != a4 { return Ok(None); }
let v24 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v25 else { return Ok(None); }
;
let v26 = fields[0];
let v27 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v32, a5, v29, a3, a4, a9, a6, a2, a1, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-mult-pow2-2"
pub fn eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9);
s.leave();
result
}
pub(super) fn case_361_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v22 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v22 { return Ok(None); }
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v32 { return Ok(None); }
let v33 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__24eo_5fpf, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__24eo_5fpf, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__24eo_5fpf, &[v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v2, v5, v8, v11, v14, v17, v20, v34, v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v92: Term, v94: Term, a0: Term, v91: Term, v89: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match eo__24eo_5fnil(s, v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v95, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v91, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v89, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(v103)) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_extract, &[a4, v104]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v105, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v102, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(v112)) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v111, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v110, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.literal(Lit::Binary(BitVec::new(0, &v116))) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v115, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v109, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v101, v119) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v120))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v66: Term, a1: Term, v67: Term, a2: Term, v60: Term, a0: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a1 { return Ok(None); }
let v72 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
let v75 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v75 { return Ok(None); }
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v80, v81)) = v79 else { return Ok(None); }
;
let v82 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v80 != v82 { return Ok(None); }
let v83 = match s.unapply(v81) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v86 { return Ok(None); }
if v85 != a1 { return Ok(None); }
if v78 != a2 { return Ok(None); }
let v87 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(v87)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v88 { return Ok(None); }
let v89 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v92, v94, a0, v91, v89, a4, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v32: Term, a3: Term, v29: Term, a1: Term, a2: Term, a7: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
if v32 != a3 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != a1 { return Ok(None); }
if v40 != a2 { return Ok(None); }
let v49 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
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
if v56 != a4 { return Ok(None); }
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
more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v66, a1, v67, a2, v60, a0, a4, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a1 { return Ok(None); }
if v15 != a2 { return Ok(None); }
let v24 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v25 else { return Ok(None); }
;
let v26 = fields[0];
let v27 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v32, a3, v29, a1, a2, a7, a4, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-mult-pow2-2b"
pub fn eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn case_362_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24eo_5fpf, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v2, v5, v8, v11, v14, v28, v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v359: Term, v357: Term, v353: Term, v352: Term, v340: Term, v328: Term, v327: Term, a8: Term) -> CheckResult<Option<Term>> {
let v360 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.literal(Lit::Binary(BitVec::new(0, &v360))) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.apply(v359, v361) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.apply(v357, v362) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match eo__24eo_5ftypeof(s, v363) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match eo__24eo_5fnil(s, v353, v364) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.apply(v352, v365) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.apply(v340, v366) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.apply(v328, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.apply(v327, v368) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.literal(Lit::Numeral(v371)) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v370, v372) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v369, v373) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v374))
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, a4: Term, v333: Term, v329: Term, a6: Term, a5: Term, a7: Term, a3: Term, a2: Term, v328: Term, v327: Term, a8: Term) -> CheckResult<Option<Term>> {
let v334 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v334, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.literal(Lit::Binary(BitVec::new(0, &v336))) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v335, v337) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.apply(v333, v338) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v329, v339) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.apply(v343, a5) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.apply(v342, v344) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v346, a7) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.literal(Lit::Binary(BitVec::new(0, &v348))) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.apply(v347, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.apply(v345, v350) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v341, v351) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.apply(v355, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.apply(v354, v356) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.apply(v358, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v359, v357, v353, v352, v340, v328, v327, a8)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v303: Term, v304: Term, a0: Term, a1: Term, a3: Term, a2: Term, a4: Term, a6: Term, a5: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
let v305 = match s.unapply(v303) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v306, v307)) = v305 else { return Ok(None); }
;
let v308 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v306 != v308 { return Ok(None); }
let v309 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.literal(Lit::Numeral(v309)) { Ok(v) => v, Err(e) => return Err(e) };
if v307 != v310 { return Ok(None); }
let v311 = match s.unapply(v304) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v312, v313)) = v311 else { return Ok(None); }
;
let v314 = match s.unapply(v312) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v315, v316)) = v314 else { return Ok(None); }
;
let v317 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v315 != v317 { return Ok(None); }
let v318 = match s.unapply(v316) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v319, v320)) = v318 else { return Ok(None); }
;
let v321 = match s.unapply(v319) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v322, v323)) = v321 else { return Ok(None); }
;
let v324 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v322 != v324 { return Ok(None); }
if v323 != a0 { return Ok(None); }
if v320 != a1 { return Ok(None); }
let v325 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.literal(Lit::Numeral(v325)) { Ok(v) => v, Err(e) => return Err(e) };
if v313 != v326 { return Ok(None); }
let v327 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.construct(Constructor::eo_extract, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v331, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v330, v332) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, a4, v333, v329, a6, a5, a7, a3, a2, v328, v327, a8)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v273: Term, v270: Term, a5: Term, v237: Term, v130: Term, a1: Term, v123: Term, a15: Term, a8: Term, a0: Term, a3: Term, a2: Term, a4: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v275 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.literal(Lit::Numeral(v275)) { Ok(v) => v, Err(e) => return Err(e) };
if v273 != v276 { return Ok(None); }
let v277 = match s.unapply(v270) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v278, v279)) = v277 else { return Ok(None); }
;
let v280 = match s.unapply(v278) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v281, v282)) = v280 else { return Ok(None); }
;
let v283 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v281 != v283 { return Ok(None); }
let v284 = match s.unapply(v282) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v285, v286)) = v284 else { return Ok(None); }
;
let v287 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v285 != v287 { return Ok(None); }
if v286 != a5 { return Ok(None); }
let v288 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.literal(Lit::Numeral(v288)) { Ok(v) => v, Err(e) => return Err(e) };
if v279 != v289 { return Ok(None); }
let v290 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.literal(Lit::Numeral(v290)) { Ok(v) => v, Err(e) => return Err(e) };
if v237 != v291 { return Ok(None); }
if v130 != a1 { return Ok(None); }
let v292 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v123 != v292 { return Ok(None); }
let v293 = match s.destruct(Constructor::eo__24eo_5fpf, a15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v293 else { return Ok(None); }
;
let v294 = fields[0];
let v295 = match s.unapply(v294) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v296, v297)) = v295 else { return Ok(None); }
;
let v298 = match s.unapply(v296) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v299, v300)) = v298 else { return Ok(None); }
;
let v301 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v299 != v301 { return Ok(None); }
if v300 != a8 { return Ok(None); }
let v302 = match s.unapply(v297) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v303, v304)) = v302 else { return Ok(None); }
;
more_8_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v303, v304, a0, a1, a3, a2, a4, a6, a5, a7, a8)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v239: Term, v240: Term, a5: Term, a6: Term, v237: Term, v130: Term, a1: Term, v123: Term, a15: Term, a8: Term, a0: Term, a3: Term, a2: Term, a4: Term, a7: Term) -> CheckResult<Option<Term>> {
let v241 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v239 != v241 { return Ok(None); }
let v242 = match s.unapply(v240) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v243, v244)) = v242 else { return Ok(None); }
;
let v245 = match s.unapply(v243) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v246, v247)) = v245 else { return Ok(None); }
;
let v248 = match s.unapply(v246) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v249, v250)) = v248 else { return Ok(None); }
;
let v251 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v249 != v251 { return Ok(None); }
let v252 = match s.unapply(v250) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v253, v254)) = v252 else { return Ok(None); }
;
let v255 = match s.unapply(v253) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v256, v257)) = v255 else { return Ok(None); }
;
let v258 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v256 != v258 { return Ok(None); }
if v257 != a5 { return Ok(None); }
let v259 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.literal(Lit::Numeral(v259)) { Ok(v) => v, Err(e) => return Err(e) };
if v254 != v260 { return Ok(None); }
if v247 != a6 { return Ok(None); }
let v261 = match s.unapply(v244) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v262, v263)) = v261 else { return Ok(None); }
;
let v264 = match s.unapply(v262) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v265, v266)) = v264 else { return Ok(None); }
;
let v267 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v265 != v267 { return Ok(None); }
if v266 != a6 { return Ok(None); }
let v268 = match s.unapply(v263) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v269, v270)) = v268 else { return Ok(None); }
;
let v271 = match s.unapply(v269) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v272, v273)) = v271 else { return Ok(None); }
;
let v274 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v272 != v274 { return Ok(None); }
more_7_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v273, v270, a5, v237, v130, a1, v123, a15, a8, a0, a3, a2, a4, a6, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v192: Term, a3: Term, v189: Term, a2: Term, v182: Term, a5: Term, a6: Term, v130: Term, a1: Term, v123: Term, a15: Term, a8: Term, a0: Term, a4: Term, a7: Term) -> CheckResult<Option<Term>> {
if v192 != a3 { return Ok(None); }
let v206 = match s.unapply(v189) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v207, v208)) = v206 else { return Ok(None); }
;
let v209 = match s.unapply(v207) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v210, v211)) = v209 else { return Ok(None); }
;
let v212 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v210 != v212 { return Ok(None); }
if v211 != a3 { return Ok(None); }
let v213 = match s.unapply(v208) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v214, v215)) = v213 else { return Ok(None); }
;
let v216 = match s.unapply(v214) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v217, v218)) = v216 else { return Ok(None); }
;
let v219 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v217 != v219 { return Ok(None); }
let v220 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.literal(Lit::Numeral(v220)) { Ok(v) => v, Err(e) => return Err(e) };
if v218 != v221 { return Ok(None); }
let v222 = match s.unapply(v215) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v223, v224)) = v222 else { return Ok(None); }
;
let v225 = match s.unapply(v223) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v226, v227)) = v225 else { return Ok(None); }
;
let v228 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v226 != v228 { return Ok(None); }
let v229 = match s.unapply(v227) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v230, v231)) = v229 else { return Ok(None); }
;
let v232 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v230 != v232 { return Ok(None); }
if v231 != a2 { return Ok(None); }
let v233 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.literal(Lit::Numeral(v233)) { Ok(v) => v, Err(e) => return Err(e) };
if v224 != v234 { return Ok(None); }
let v235 = match s.unapply(v182) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v236, v237)) = v235 else { return Ok(None); }
;
let v238 = match s.unapply(v236) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v239, v240)) = v238 else { return Ok(None); }
;
more_6_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v239, v240, a5, a6, v237, v130, a1, v123, a15, a8, a0, a3, a2, a4, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v170: Term, a4: Term, v167: Term, v153: Term, v137: Term, a2: Term, a3: Term, a5: Term, a6: Term, v130: Term, a1: Term, v123: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v172 = match s.unapply(v170) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v173, v174)) = v172 else { return Ok(None); }
;
let v175 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v173 != v175 { return Ok(None); }
if v174 != a4 { return Ok(None); }
let v176 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(v176)) { Ok(v) => v, Err(e) => return Err(e) };
if v167 != v177 { return Ok(None); }
let v178 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.literal(Lit::Numeral(v178)) { Ok(v) => v, Err(e) => return Err(e) };
if v153 != v179 { return Ok(None); }
let v180 = match s.unapply(v137) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v181, v182)) = v180 else { return Ok(None); }
;
let v183 = match s.unapply(v181) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v184, v185)) = v183 else { return Ok(None); }
;
let v186 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v184 != v186 { return Ok(None); }
let v187 = match s.unapply(v185) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v188, v189)) = v187 else { return Ok(None); }
;
let v190 = match s.unapply(v188) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v191, v192)) = v190 else { return Ok(None); }
;
let v193 = match s.unapply(v191) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v194, v195)) = v193 else { return Ok(None); }
;
let v196 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v194 != v196 { return Ok(None); }
let v197 = match s.unapply(v195) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v198, v199)) = v197 else { return Ok(None); }
;
let v200 = match s.unapply(v198) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v201, v202)) = v200 else { return Ok(None); }
;
let v203 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v201 != v203 { return Ok(None); }
if v202 != a2 { return Ok(None); }
let v204 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.literal(Lit::Numeral(v204)) { Ok(v) => v, Err(e) => return Err(e) };
if v199 != v205 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v192, a3, v189, a2, v182, a5, a6, v130, a1, v123, a15, a8, a0, a4, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v132: Term, v134: Term, v133: Term, a3: Term, a4: Term, a2: Term, a5: Term, a6: Term, v130: Term, a1: Term, v123: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
if v132 != v134 { return Ok(None); }
let v135 = match s.unapply(v133) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v136, v137)) = v135 else { return Ok(None); }
;
let v138 = match s.unapply(v136) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v139, v140)) = v138 else { return Ok(None); }
;
let v141 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v139 != v141 { return Ok(None); }
let v142 = match s.unapply(v140) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v143, v144)) = v142 else { return Ok(None); }
;
let v145 = match s.unapply(v143) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v146, v147)) = v145 else { return Ok(None); }
;
let v148 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v146 != v148 { return Ok(None); }
let v149 = match parse_int("2") { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Numeral(v149)) { Ok(v) => v, Err(e) => return Err(e) };
if v147 != v150 { return Ok(None); }
let v151 = match s.unapply(v144) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v152, v153)) = v151 else { return Ok(None); }
;
let v154 = match s.unapply(v152) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v155, v156)) = v154 else { return Ok(None); }
;
let v157 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v155 != v157 { return Ok(None); }
let v158 = match s.unapply(v156) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v159, v160)) = v158 else { return Ok(None); }
;
let v161 = match s.unapply(v159) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v162, v163)) = v161 else { return Ok(None); }
;
let v164 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v162 != v164 { return Ok(None); }
if v163 != a3 { return Ok(None); }
let v165 = match s.unapply(v160) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v166, v167)) = v165 else { return Ok(None); }
;
let v168 = match s.unapply(v166) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v169, v170)) = v168 else { return Ok(None); }
;
let v171 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v169 != v171 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v170, a4, v167, v153, v137, a2, a3, a5, a6, v130, a1, v123, a15, a8, a0, a7)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, a13: Term, a5: Term, a6: Term, a14: Term, a3: Term, a4: Term, a2: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v98 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v98 else { return Ok(None); }
;
let v99 = fields[0];
let v100 = match s.unapply(v99) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v101, v102)) = v100 else { return Ok(None); }
;
let v103 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v104, v105)) = v103 else { return Ok(None); }
;
let v106 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v104 != v106 { return Ok(None); }
let v107 = match s.unapply(v105) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v108, v109)) = v107 else { return Ok(None); }
;
let v110 = match s.unapply(v108) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v111 != v113 { return Ok(None); }
if v112 != a5 { return Ok(None); }
let v114 = match s.unapply(v109) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v115, v116)) = v114 else { return Ok(None); }
;
let v117 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v115 != v117 { return Ok(None); }
if v116 != a6 { return Ok(None); }
let v118 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v102 != v118 { return Ok(None); }
let v119 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v119 else { return Ok(None); }
;
let v120 = fields[0];
let v121 = match s.unapply(v120) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v122, v123)) = v121 else { return Ok(None); }
;
let v124 = match s.unapply(v122) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v125, v126)) = v124 else { return Ok(None); }
;
let v127 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v125 != v127 { return Ok(None); }
let v128 = match s.unapply(v126) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v129, v130)) = v128 else { return Ok(None); }
;
let v131 = match s.unapply(v129) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v132, v133)) = v131 else { return Ok(None); }
;
let v134 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v132, v134, v133, a3, a4, a2, a5, a6, v130, a1, v123, a15, a8, a0, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v68: Term, a2: Term, v69: Term, a3: Term, v62: Term, a12: Term, a5: Term, a13: Term, a6: Term, a14: Term, a4: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v70 = match s.unapply(v68) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v71, v72)) = v70 else { return Ok(None); }
;
let v73 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v71 != v73 { return Ok(None); }
if v72 != a2 { return Ok(None); }
let v74 = match s.unapply(v69) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v75, v76)) = v74 else { return Ok(None); }
;
let v77 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v77 { return Ok(None); }
if v76 != a3 { return Ok(None); }
let v78 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v78 { return Ok(None); }
let v79 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v79 else { return Ok(None); }
;
let v80 = fields[0];
let v81 = match s.unapply(v80) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v82, v83)) = v81 else { return Ok(None); }
;
let v84 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v85, v86)) = v84 else { return Ok(None); }
;
let v87 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v85 != v87 { return Ok(None); }
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v92, v93)) = v91 else { return Ok(None); }
;
let v94 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v92 != v94 { return Ok(None); }
if v93 != a5 { return Ok(None); }
let v95 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Numeral(v95)) { Ok(v) => v, Err(e) => return Err(e) };
if v90 != v96 { return Ok(None); }
let v97 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v83 != v97 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, a13, a5, a6, a14, a3, a4, a2, a1, a15, a8, a0, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v11: Term, v4: Term, a10: Term, a2: Term, a11: Term, a3: Term, a12: Term, a5: Term, a13: Term, a6: Term, a14: Term, a4: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v36 = match parse_int("64") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Numeral(v36)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v37 { return Ok(None); }
let v38 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v38 { return Ok(None); }
let v39 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v39 else { return Ok(None); }
;
let v40 = fields[0];
let v41 = match s.unapply(v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v47 { return Ok(None); }
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
if v53 != a2 { return Ok(None); }
let v55 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(v55)) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v56 { return Ok(None); }
let v57 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v43 != v57 { return Ok(None); }
let v58 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v58 else { return Ok(None); }
;
let v59 = fields[0];
let v60 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.unapply(v61) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v64, v65)) = v63 else { return Ok(None); }
;
let v66 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v64 != v66 { return Ok(None); }
let v67 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v68, a2, v69, a3, v62, a12, a5, a13, a6, a14, a4, a1, a15, a8, a0, a7)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term, a15: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a3 { return Ok(None); }
let v23 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.unapply(v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a4 { return Ok(None); }
let v34 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v35 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v11, v4, a10, a2, a11, a3, a12, a5, a13, a6, a14, a4, a1, a15, a8, a0, a7)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term, a15: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-mult-leading-bit"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term, a12: Term, a13: Term, a14: Term, a15: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
s.leave();
result
}
pub(super) fn more_8_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v33: Term, v36: Term, v39: Term, v42: Term, v45: Term, v48: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v52: Term) -> CheckResult<Option<Term>> {
let v53 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__24eo_5fpf, &[v53]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__24eo_5fpf, &[v55]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__24eo_5fpf, &[v57]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__24eo_5fpf, &[v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__24eo_5fpf, &[v61]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__24eo_5fpf, &[v63]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v2, v5, v8, v11, v14, v17, v20, v23, v26, v52, v54, v56, v58, v60, v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v65))
}
pub(super) fn case_363_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v28 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v28 { return Ok(None); }
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
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
let v47 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v47 else { return Ok(None); }
;
let v48 = fields[0];
let v49 = fields[1];
let v50 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v50 { return Ok(None); }
let v51 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__24eo_5fpf, &[v51]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v33, v36, v39, v42, v45, v48, v2, v5, v8, v11, v14, v17, v20, v23, v26, v52)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a2: Term, a1: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v64 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v66, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v64, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(v73)) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v72, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v71, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v78, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v77, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Binary(BitVec::new(0, &v81))) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v76, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v70, v84) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v85))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, v18: Term, v32: Term, a7: Term, a3: Term, a1: Term, a8: Term, a4: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
if v18 != v32 { return Ok(None); }
let v33 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v33 else { return Ok(None); }
;
let v34 = fields[0];
let v35 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
if v40 != a3 { return Ok(None); }
let v42 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v43 != v45 { return Ok(None); }
if v44 != a1 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
let v48 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
if v53 != a4 { return Ok(None); }
let v55 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a2 { return Ok(None); }
let v62 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(v62)) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v63 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, a0, a2, a1, a3, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.unapply(v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a1 { return Ok(None); }
let v30 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v31 { return Ok(None); }
let v32 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, v18, v32, a7, a3, a1, a8, a4, a2, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, a0, a1, a2, a3, a4, a5, a6, a7, a8) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-udiv-pow2-not-one"
pub fn eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, a0, a1, a2, a3, a4, a5, a6, a7, a8);
s.leave();
result
}
pub(super) fn case_364_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v38 = match eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, v2, v5, v8, v11, v14, v31, v33, v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dudiv_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-udiv-zero"
pub fn eo__24eo_5fprog_5fbv_2dudiv_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dudiv_2dzero(s, a0, a1);
s.leave();
result
}
pub(super) fn case_365_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fudiv_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dudiv_2dzero(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dudiv_2done(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dudiv_2done(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dudiv_2done(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-udiv-one"
pub fn eo__24eo_5fprog_5fbv_2dudiv_2done(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dudiv_2done(s, a0, a1);
s.leave();
result
}
pub(super) fn case_366_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fudiv_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dudiv_2done(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v88: Term, v92: Term, v87: Term, v81: Term) -> CheckResult<Option<Term>> {
let v93 = match s.apply(v88, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.literal(Lit::Binary(BitVec::new(0, &v94))) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v93, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v87, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v81, v97) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v98))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v66: Term, v67: Term, a1: Term, v64: Term, a0: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v68 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v66 != v68 { return Ok(None); }
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
if v71 != a1 { return Ok(None); }
let v73 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(v73)) { Ok(v) => v, Err(e) => return Err(e) };
if v64 != v74 { return Ok(None); }
let v75 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v78, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v77, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v75, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Numeral(v84)) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v83, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v82, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Numeral(v89)) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_extract, &[a4, v90]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v88, v92, v87, v81)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v18: Term, v32: Term, a7: Term, a3: Term, a2: Term, a1: Term, a8: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
if v18 != v32 { return Ok(None); }
let v33 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v33 else { return Ok(None); }
;
let v34 = fields[0];
let v35 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
if v40 != a3 { return Ok(None); }
let v42 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != a2 { return Ok(None); }
let v49 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v52 { return Ok(None); }
if v51 != a1 { return Ok(None); }
let v53 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v60 != a4 { return Ok(None); }
let v62 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v66, v67, a1, v64, a0, a2, a3, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_int_2eispow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.unapply(v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a1 { return Ok(None); }
let v30 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v31 { return Ok(None); }
let v32 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v18, v32, a7, a3, a2, a1, a8, a4, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, a0, a1, a2, a3, a4, a5, a6, a7, a8) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-urem-pow2-not-one"
pub fn eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, a0, a1, a2, a3, a4, a5, a6, a7, a8);
s.leave();
result
}
pub(super) fn case_367_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v38 = match eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v2, v5, v8, v11, v14, v31, v33, v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn cases_45_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_360_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_361_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_362_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_363_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_364_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_365_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_366_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_367_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2durem_2done(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2durem_2done(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2durem_2done(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-urem-one"
pub fn eo__24eo_5fprog_5fbv_2durem_2done(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2durem_2done(s, a0, a1);
s.leave();
result
}
pub(super) fn case_368_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5furem_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2durem_2done(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2durem_2dself(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2durem_2dself(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2durem_2dself(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-urem-self"
pub fn eo__24eo_5fprog_5fbv_2durem_2dself(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2durem_2dself(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_369_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5furem_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fbv_2durem_2dself(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dshl_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dshl_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dshl_2dzero(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-shl-zero"
pub fn eo__24eo_5fprog_5fbv_2dshl_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dshl_2dzero(s, a0, a1);
s.leave();
result
}
pub(super) fn case_370_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fshl_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dshl_2dzero(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dlshr_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dlshr_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dlshr_2dzero(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-lshr-zero"
pub fn eo__24eo_5fprog_5fbv_2dlshr_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dlshr_2dzero(s, a0, a1);
s.leave();
result
}
pub(super) fn case_371_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5flshr_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dlshr_2dzero(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dashr_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dashr_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dashr_2dzero(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ashr-zero"
pub fn eo__24eo_5fprog_5fbv_2dashr_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dashr_2dzero(s, a0, a1);
s.leave();
result
}
pub(super) fn case_372_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fashr_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dashr_2dzero(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dugt_2durem(s: &mut Store, v23: Term, v27: Term, v21: Term, a0: Term, a2: Term, v20: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v23, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v21, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_bvugt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v32, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v30, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v29, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v20, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dugt_2durem(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.construct(Constructor::eo_bvugt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v13, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dugt_2durem(s, v23, v27, v21, a0, a2, v20)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dugt_2durem(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dugt_2durem(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ugt-urem"
pub fn eo__24eo_5fprog_5fbv_2dugt_2durem(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dugt_2durem(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_373_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fugt_5furem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v17 = match eo__24eo_5fprog_5fbv_2dugt_2durem(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dult_2done(s: &mut Store, v23: Term, v30: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v31 = match s.apply(v23, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(v35)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v33, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v31, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2done(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v22 { return Ok(None); }
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(v27)) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dult_2done(s, v23, v30, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dult_2done(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dult_2done(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ult-one"
pub fn eo__24eo_5fprog_5fbv_2dult_2done(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dult_2done(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_374_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fult_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fbv_2dult_2done(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s: &mut Store, a3: Term, a0: Term, v30: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a2 { return Ok(None); }
let v23 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_sign_5fextend, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s, a3, a0, v30)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-merge-sign-extend-1"
pub fn eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_375_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn cases_46_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_368_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_369_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_370_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_371_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_372_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_373_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_374_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_375_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s: &mut Store, v33: Term, a1: Term, v30: Term, a2: Term, a0: Term, a3: Term) -> CheckResult<Option<Term>> {
if v33 != a1 { return Ok(None); }
let v35 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
if v40 != a2 { return Ok(None); }
let v42 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Numeral(v42)) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v43 { return Ok(None); }
let v44 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_zero_5fextend, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v44, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_zero_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v52))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a2 { return Ok(None); }
let v16 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(v16)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v17 { return Ok(None); }
let v18 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v18 { return Ok(None); }
let v19 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
if v26 != a3 { return Ok(None); }
let v28 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v34 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, v33, a1, v30, a2, a0, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-merge-sign-extend-2"
pub fn eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn case_376_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, v111: Term, v117: Term, v109: Term, v108: Term, v75: Term) -> CheckResult<Option<Term>> {
let v118 = match s.apply(v111, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v109, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v119, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v108, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v75, v122) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v123))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a6: Term, a5: Term, a3: Term, a2: Term, v91: Term, a4: Term, v90: Term, v89: Term, v76: Term, a0: Term, v75: Term) -> CheckResult<Option<Term>> {
let v92 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v91, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(v99)) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v98, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v97, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v96, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v90, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v104, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v89, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v76, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(v112)) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_extract, &[a5, v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v114, v116) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v111, v117, v109, v108, v75)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a1: Term, a0: Term, a3: Term, a2: Term, a6: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v67 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v72, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v71, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v67, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v79, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v78, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(v85)) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v84, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v83, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v77, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, a6, a5, a3, a2, v91, a4, v90, v89, v76, a0, v75)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, v34: Term, a5: Term, v31: Term, a0: Term, a9: Term, a6: Term, a3: Term, a1: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
if v34 != a5 { return Ok(None); }
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
let v46 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a0 { return Ok(None); }
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v48 { return Ok(None); }
let v49 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
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
if v56 != a6 { return Ok(None); }
let v58 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
if v63 != a3 { return Ok(None); }
let v65 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(v65)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v66 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, a1, a0, a3, a2, a6, a5, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
if v7 != a4 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v24 { return Ok(None); }
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v26 { return Ok(None); }
let v27 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v27 else { return Ok(None); }
;
let v28 = fields[0];
let v29 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v33, v34)) = v32 else { return Ok(None); }
;
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v35 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v34, a5, v31, a0, a9, a6, a3, a1, a2, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sign-extend-eq-const-1"
pub fn eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9);
s.leave();
result
}
pub(super) fn case_377_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v22 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v22 { return Ok(None); }
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v32 { return Ok(None); }
let v33 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__24eo_5fpf, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__24eo_5fpf, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__24eo_5fpf, &[v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v2, v5, v8, v11, v14, v17, v20, v34, v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, v111: Term, v117: Term, v109: Term, v108: Term, v75: Term) -> CheckResult<Option<Term>> {
let v118 = match s.apply(v111, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v109, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v119, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v108, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v75, v122) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v123))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a6: Term, a5: Term, a3: Term, a2: Term, v91: Term, a4: Term, v90: Term, v89: Term, v76: Term, a0: Term, v75: Term) -> CheckResult<Option<Term>> {
let v92 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v91, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(v99)) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v98, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v97, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v96, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v90, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v104, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v89, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v76, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(v112)) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_extract, &[a5, v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v114, v116) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v111, v117, v109, v108, v75)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a3: Term, a2: Term, a1: Term, a0: Term, a6: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v67 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v72, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v71, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v67, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v79, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v78, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(v85)) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v84, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v83, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v77, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, a6, a5, a3, a2, v91, a4, v90, v89, v76, a0, v75)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, v34: Term, a5: Term, v31: Term, a0: Term, a9: Term, a6: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
if v34 != a5 { return Ok(None); }
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
let v46 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a0 { return Ok(None); }
let v47 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v48 { return Ok(None); }
let v49 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
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
if v56 != a6 { return Ok(None); }
let v58 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
if v63 != a3 { return Ok(None); }
let v65 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(v65)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v66 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, a3, a2, a1, a0, a6, a5, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
if v7 != a4 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(v23)) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v24 { return Ok(None); }
let v25 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v26 { return Ok(None); }
let v27 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v27 else { return Ok(None); }
;
let v28 = fields[0];
let v29 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v33, v34)) = v32 else { return Ok(None); }
;
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v35 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v34, a5, v31, a0, a9, a6, a3, a2, a1, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sign-extend-eq-const-2"
pub fn eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9);
s.leave();
result
}
pub(super) fn case_378_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v22 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v22 { return Ok(None); }
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = fields[1];
let v32 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v32 { return Ok(None); }
let v33 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__24eo_5fpf, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__24eo_5fpf, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__24eo_5fpf, &[v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v2, v5, v8, v11, v14, v17, v20, v34, v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, v55: Term, v59: Term, v49: Term, a0: Term, a4: Term, a3: Term, a2: Term, v48: Term) -> CheckResult<Option<Term>> {
let v60 = match s.apply(v55, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v49, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(v65)) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_extract, &[a4, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v64, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v62, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v72, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v61, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v48, v75) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v76))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, v35: Term, v36: Term, a3: Term, v33: Term, a1: Term, a0: Term, a2: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v37 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a3 { return Ok(None); }
let v38 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(v38)) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v39 { return Ok(None); }
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v40, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_extract, &[a5, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v51, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v50, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v55, v59, v49, a0, a4, a3, a2, v48)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a4 { return Ok(None); }
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
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
if v29 != a5 { return Ok(None); }
let v31 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v35, v36, a3, v33, a1, a0, a2, a5, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-zero-extend-eq-const-1"
pub fn eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn case_379_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v19 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v19 { return Ok(None); }
let v20 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v20 else { return Ok(None); }
;
let v21 = fields[0];
let v22 = fields[1];
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v2, v5, v8, v11, v14, v17, v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, v55: Term, v59: Term, v49: Term, a0: Term, a4: Term, a3: Term, a2: Term, v48: Term) -> CheckResult<Option<Term>> {
let v60 = match s.apply(v55, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v49, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(v65)) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_extract, &[a4, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v64, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v62, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v72, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v61, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v48, v75) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v76))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, v35: Term, v36: Term, a3: Term, v33: Term, a2: Term, a1: Term, a0: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v37 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a3 { return Ok(None); }
let v38 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(v38)) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v39 { return Ok(None); }
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v40, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_extract, &[a5, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v51, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v50, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v55, v59, v49, a0, a4, a3, a2, v48)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
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
if v7 != a4 { return Ok(None); }
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
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
if v29 != a5 { return Ok(None); }
let v31 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v35, v36, a3, v33, a2, a1, a0, a5, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-zero-extend-eq-const-2"
pub fn eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn case_380_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v19 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v19 { return Ok(None); }
let v20 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v20 else { return Ok(None); }
;
let v21 = fields[0];
let v22 = fields[1];
let v23 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v23 else { return Ok(None); }
;
let v24 = fields[0];
let v25 = fields[1];
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v2, v5, v8, v11, v14, v17, v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, a4: Term, a3: Term, a2: Term, v64: Term, v62: Term) -> CheckResult<Option<Term>> {
let v65 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(v65)) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_extract, &[a4, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v64, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v62, v71) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v72))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, v33: Term, a2: Term, v26: Term, a1: Term, a4: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
if v33 != a2 { return Ok(None); }
let v36 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.destruct(Constructor::eo_zero_5fextend, v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v39 else { return Ok(None); }
;
let v40 = fields[0];
if v40 != a1 { return Ok(None); }
let v41 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.destruct(Constructor::eo_extract, v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v44 else { return Ok(None); }
;
let v45 = fields[0];
let v46 = fields[1];
if v45 != a4 { return Ok(None); }
let v47 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
let v49 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.destruct(Constructor::eo_int_5fto_5fbv, v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v52 else { return Ok(None); }
;
let v53 = fields[0];
if v53 != a3 { return Ok(None); }
if v51 != a2 { return Ok(None); }
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v54, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, a4, a3, a2, v64, v62)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
if v7 != a4 { return Ok(None); }
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
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
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.destruct(Constructor::eo_int_5fto_5fbv, v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v34 else { return Ok(None); }
;
let v35 = fields[0];
if v35 != a3 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, v33, a2, v26, a1, a4, a3, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-zero-extend-ult-const-1"
pub fn eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn case_381_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v23 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, v2, v5, v8, v11, v14, v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, a4: Term, v65: Term, a3: Term, a2: Term, v63: Term, a0: Term, v62: Term) -> CheckResult<Option<Term>> {
let v66 = match s.construct(Constructor::eo_extract, &[a4, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v66, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v63, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v62, v71) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v72))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, v33: Term, a2: Term, v26: Term, a1: Term, a4: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
if v33 != a2 { return Ok(None); }
let v36 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.destruct(Constructor::eo_zero_5fextend, v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v39 else { return Ok(None); }
;
let v40 = fields[0];
if v40 != a1 { return Ok(None); }
let v41 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.destruct(Constructor::eo_extract, v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v44 else { return Ok(None); }
;
let v45 = fields[0];
let v46 = fields[1];
if v45 != a4 { return Ok(None); }
let v47 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
let v49 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.destruct(Constructor::eo_int_5fto_5fbv, v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v52 else { return Ok(None); }
;
let v53 = fields[0];
if v53 != a3 { return Ok(None); }
if v51 != a2 { return Ok(None); }
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v54, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(v64)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, a4, v65, a3, a2, v63, a0, v62)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
if v7 != a4 { return Ok(None); }
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
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v21 { return Ok(None); }
let v22 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
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
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.destruct(Constructor::eo_int_5fto_5fbv, v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v34 else { return Ok(None); }
;
let v35 = fields[0];
if v35 != a3 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, v33, a2, v26, a1, a4, a3, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-zero-extend-ult-const-2"
pub fn eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn case_382_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v23 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, v2, v5, v8, v11, v14, v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, a1: Term, a0: Term, a3: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v139 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v140, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v144, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v143, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v139, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v148, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Numeral(v150)) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_extract, &[a4, v151]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v153, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v152, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v149, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v147, v156) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v157))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v110: Term, v112: Term, v111: Term, a0: Term, v104: Term, v62: Term, v4: Term, a6: Term, a4: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v110 != v112 { return Ok(None); }
if v111 != a0 { return Ok(None); }
let v113 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(v113)) { Ok(v) => v, Err(e) => return Err(e) };
if v104 != v114 { return Ok(None); }
let v115 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v115 { return Ok(None); }
let v116 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v116 { return Ok(None); }
let v117 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v117 else { return Ok(None); }
;
let v118 = fields[0];
let v119 = match s.unapply(v118) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v120, v121)) = v119 else { return Ok(None); }
;
let v122 = match s.unapply(v120) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v123, v124)) = v122 else { return Ok(None); }
;
let v125 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v123 != v125 { return Ok(None); }
if v124 != a4 { return Ok(None); }
let v126 = match s.unapply(v121) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v127, v128)) = v126 else { return Ok(None); }
;
let v129 = match s.unapply(v127) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v130, v131)) = v129 else { return Ok(None); }
;
let v132 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v130 != v132 { return Ok(None); }
let v133 = match s.unapply(v131) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v134, v135)) = v133 else { return Ok(None); }
;
let v136 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v134 != v136 { return Ok(None); }
if v135 != a0 { return Ok(None); }
let v137 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Numeral(v137)) { Ok(v) => v, Err(e) => return Err(e) };
if v128 != v138 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, a1, a0, a3, a2, a4)
}
