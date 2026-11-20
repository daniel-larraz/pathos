//! Generated functions, module 10 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s: &mut Store, v4: Term, a1: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s, v24, v27, v19, a0, v18, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
if v11 != a1 { return Ok(None); }
more_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s, v4, a1, a2, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-concat-star-nullable1"
pub fn eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_177_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_544_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_177_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_2_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s: &mut Store, v31: Term, v39: Term, v30: Term) -> CheckResult<Option<Term>> {
let v40 = match s.builtin_list(EvalOp::ListSingletonElim, &[v31, v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v30, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s: &mut Store, v21: Term, v27: Term, v19: Term, a0: Term, v18: Term, a2: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v21, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListConcat, &[v19, a0, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v18, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v33, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_list(EvalOp::ListConcat, &[v32, a0, v38]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s, v31, v39, v30)
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s: &mut Store, v4: Term, a1: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s, v21, v27, v19, a0, v18, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
if v11 != a1 { return Ok(None); }
more_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s, v4, a1, a2, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-concat-star-nullable2"
pub fn eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_178_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable2(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_545_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_178_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s: &mut Store, v19: Term, v23: Term, v17: Term, v16: Term, a3: Term, v15: Term, a0: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_list(EvalOp::ListConcat, &[v15, a0, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListSingletonElim, &[v14, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v13, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s: &mut Store, v1: Term, a0: Term, v11: Term, v0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s, v19, v23, v17, v16, a3, v15, a0, v14, v13)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s, v1, a0, v11, v0, a1, a2, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-concat-merge"
pub fn eo__24eo_5fprog_5fre_2dconcat_2dmerge(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dconcat_2dmerge(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_546_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fconcat_5fmerge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fre_2dconcat_2dmerge(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dunion_2dall(s: &mut Store, v10: Term, v11: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dunion_2dall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dunion_2dall(s, v10, v11, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dunion_2dall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dunion_2dall(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-union-all"
pub fn eo__24eo_5fprog_5fre_2dunion_2dall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dunion_2dall(s, a0, a1);
s.leave();
result
}
pub(super) fn case_547_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funion_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fre_2dunion_2dall(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_136_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_544_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_545_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_546_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_547_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s: &mut Store, v27: Term, a0: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s: &mut Store, v4: Term, v16: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s, v27, a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s, v4, v16, a1, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-union-const-elim"
pub fn eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_548_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funion_5fconst_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fre_2dunion_2dconst_2delim(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dinter_2dall(s: &mut Store, v11: Term, a0: Term, a1: Term, v10: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v11, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonElim, &[v10, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dinter_2dall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dinter_2dall(s, v11, a0, a1, v10, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dinter_2dall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dinter_2dall(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-inter-all"
pub fn eo__24eo_5fprog_5fre_2dinter_2dall(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dinter_2dall(s, a0, a1);
s.leave();
result
}
pub(super) fn case_549_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5finter_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fre_2dinter_2dall(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_179_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v8: Term, v7: Term) -> CheckResult<Option<Term>> {
let v9 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_550_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fstar_5fnone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v2 { return Ok(None); }
let v3 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_179_eo__24eo_5fcmd_5fstep_5fproven(s, v8, v7)
}
pub(super) fn more_180_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v3: Term, v8: Term) -> CheckResult<Option<Term>> {
let v9 = match s.apply(v3, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_551_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fstar_5femp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v2 { return Ok(None); }
let v3 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
more_180_eo__24eo_5fcmd_5fstep_5fproven(s, v3, v8)
}
pub(super) fn cases_0_137_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_548_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_549_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_550_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_551_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dstar_2dstar(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dstar_2dstar(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dstar_2dstar(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-star-star"
pub fn eo__24eo_5fprog_5fre_2dstar_2dstar(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dstar_2dstar(s, a0);
s.leave();
result
}
pub(super) fn case_552_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fstar_5fstar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2dstar_2dstar(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2drange_2drefl(s: &mut Store, a0: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2drange_2drefl(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2drange_2drefl(s, a0, v14)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2drange_2drefl(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2drange_2drefl(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-range-refl"
pub fn eo__24eo_5fprog_5fre_2drange_2drefl(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2drange_2drefl(s, a0, a1);
s.leave();
result
}
pub(super) fn case_553_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5frange_5frefl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fre_2drange_2drefl(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_2_eo__24eo_5fprog_5fre_2drange_2demp(s: &mut Store, v49: Term, v50: Term, a0: Term, v32: Term, a1: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
if v50 != a0 { return Ok(None); }
let v52 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v52 { return Ok(None); }
let v53 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v53, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v59))
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2drange_2demp(s: &mut Store, v31: Term, a1: Term, a0: Term, v32: Term) -> CheckResult<Option<Term>> {
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
let v36 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v41 != v43 { return Ok(None); }
let v44 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v47 { return Ok(None); }
if v46 != a1 { return Ok(None); }
let v48 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fre_2drange_2demp(s, v49, v50, a0, v32, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2drange_2demp(s: &mut Store, v15: Term, a1: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
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
let v26 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a1 { return Ok(None); }
let v27 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v27 { return Ok(None); }
let v28 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v28 else { return Ok(None); }
;
let v29 = fields[0];
let v30 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fre_2drange_2demp(s, v31, a1, a0, v32)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2drange_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fre_2drange_2demp(s, v15, a1, a4, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2drange_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2drange_2demp(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-range-emp"
pub fn eo__24eo_5fprog_5fre_2drange_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2drange_2demp(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_181_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v12: Term, v15: Term, v2: Term, v5: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24eo_5fpf, &[v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24eo_5fprog_5fre_2drange_2demp(s, v2, v5, v19, v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_554_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5frange_5femp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
let v16 = fields[1];
let v17 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v17 { return Ok(None); }
let v18 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
more_181_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v12, v15, v2, v5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s: &mut Store, v18: Term, a0: Term, v11: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s, v18, a0, v11, v4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-range-non-singleton-1"
pub fn eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_555_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d1(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn cases_0_138_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_552_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_553_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_554_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_555_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s: &mut Store, v18: Term, a1: Term, v11: Term, v4: Term, a0: Term) -> CheckResult<Option<Term>> {
if v18 != a1 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s, v18, a1, v11, v4, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-range-non-singleton-2"
pub fn eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_556_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fre_2drange_2dnon_2dsingleton_2d2(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s: &mut Store, v10: Term, v11: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListConcat, &[v2, a0, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s, v10, v11, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-star-union-char"
pub fn eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s, a0, a1);
s.leave();
result
}
pub(super) fn case_557_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fstar_5funion_5fchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fre_2dstar_2dunion_2dchar(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s: &mut Store, a0: Term, a1: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListConcat, &[v14, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListSingletonElim, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListConcat, &[v2, a0, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v1, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s, a0, a1, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-star-union-drop-emp"
pub fn eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s, a0, a1);
s.leave();
result
}
pub(super) fn case_558_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fre_2dstar_2dunion_2ddrop_2demp(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dloop_2dneg(s: &mut Store, v4: Term, v16: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_re_2eloop, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dloop_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a0 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dloop_2dneg(s, v4, v16, a0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dloop_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dloop_2dneg(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-loop-neg"
pub fn eo__24eo_5fprog_5fre_2dloop_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dloop_2dneg(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_182_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fre_2dloop_2dneg(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_559_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5floop_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_182_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn cases_0_139_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_556_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_557_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_558_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_559_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_34_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_136_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_137_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_138_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_139_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dloop_2dstar(s: &mut Store, v28: Term, v33: Term, v21: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v28 != v33 { return Ok(None); }
let v34 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v34 { return Ok(None); }
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_re_2eloop, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v35, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v43))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dloop_2dstar(s: &mut Store, v4: Term, v16: Term, a4: Term, a1: Term, a0: Term, a2: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.unapply(v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v32 { return Ok(None); }
if v31 != a1 { return Ok(None); }
let v33 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2dloop_2dstar(s, v28, v33, v21, a0, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dloop_2dstar(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v11 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2dloop_2dstar(s, v4, v16, a4, a1, a0, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dloop_2dstar(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dloop_2dstar(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-loop-star"
pub fn eo__24eo_5fprog_5fre_2dloop_2dstar(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dloop_2dstar(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_183_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fre_2dloop_2dstar(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_560_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5floop_5fstar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_183_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_2_eo__24eo_5fprog_5fre_2dinter_2dcstring(s: &mut Store, a2: Term, v44: Term) -> CheckResult<Option<Term>> {
let v45 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dinter_2dcstring(s: &mut Store, v4: Term, a2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v34 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v34 { return Ok(None); }
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v39, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v35, v43) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fre_2dinter_2dcstring(s, a2, v44)
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dinter_2dcstring(s: &mut Store, v20: Term, v21: Term, a2: Term, v18: Term, a0: Term, a1: Term, v4: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a2 { return Ok(None); }
let v27 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a0 { return Ok(None); }
if v29 != a1 { return Ok(None); }
more_1_eo__24eo_5fprog_5fre_2dinter_2dcstring(s, v4, a2, a0, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a2 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fre_2dinter_2dcstring(s, v20, v21, a2, v18, a0, a1, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dinter_2dcstring(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-inter-cstring"
pub fn eo__24eo_5fprog_5fre_2dinter_2dcstring(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dinter_2dcstring(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_184_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fre_2dinter_2dcstring(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_561_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5finter_5fcstring, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_184_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_2_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s: &mut Store, v44: Term) -> CheckResult<Option<Term>> {
let v45 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v46))
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s: &mut Store, v4: Term, a2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v34 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v34 { return Ok(None); }
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v39, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v35, v43) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s, v44)
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s: &mut Store, v20: Term, v21: Term, a2: Term, v18: Term, a0: Term, a1: Term, v4: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a2 { return Ok(None); }
let v27 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a0 { return Ok(None); }
if v29 != a1 { return Ok(None); }
more_1_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s, v4, a2, a0, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a2 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s, v20, v21, a2, v18, a0, a1, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-inter-cstring-neg"
pub fn eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_185_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_562_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5finter_5fcstring_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_185_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s: &mut Store, a0: Term, a2: Term, a3: Term, v44: Term) -> CheckResult<Option<Term>> {
let v45 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v44, v48) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v49))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s: &mut Store, v29: Term, v34: Term, v4: Term, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if v29 != v34 { return Ok(None); }
let v35 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v35 { return Ok(None); }
let v36 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v37, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v36, v43) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s, a0, a2, a3, v44)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s: &mut Store, v18: Term, a0: Term, v11: Term, a2: Term, a3: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a2 { return Ok(None); }
let v27 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a3 { return Ok(None); }
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s, v29, v34, v4, a0, a1, a2, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s, v18, a0, v11, a2, a3, v4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-len-include"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_186_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_563_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_186_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_140_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_560_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_561_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_562_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_563_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s: &mut Store, a0: Term, v52: Term, v35: Term, v33: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match eo__24eo_5fnil(s, v53, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v52, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v35, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v33, v57) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s: &mut Store, v40: Term, a2: Term, v38: Term, v37: Term, a3: Term, a0: Term, v36: Term, v35: Term, v33: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v40, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_list(EvalOp::ListSingletonElim, &[v38, v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v37, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v43, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v45, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v36, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s, a0, v52, v35, v33)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s: &mut Store, v22: Term, v28: Term, a3: Term, v21: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v22, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v21, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s, v40, a2, v38, v37, a3, a0, v36, v35, v33)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s, v22, v28, a3, v21, a0, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v14 != a3 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s, v17, v19, v18, a0, v4, a1, a2, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-len-include-pre"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_187_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dinclude_2dpre(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_564_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_187_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s: &mut Store, v28: Term, a1: Term, a0: Term, v26: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v26, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s, v28, a1, a0, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
if v14 != a2 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s, v17, v19, v18, a0, v4, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-len-norm"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_188_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2dsubstr_2dlen_2dnorm(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_565_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_188_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2dlen_2drev(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2dlen_2drev(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2dlen_2drev(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-len-rev"
pub fn eo__24eo_5fprog_5fseq_2dlen_2drev(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2dlen_2drev(s, a0);
s.leave();
result
}
pub(super) fn case_566_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5flen_5frev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fseq_2dlen_2drev(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2drev_2drev(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2drev_2drev(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2drev_2drev(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-rev-rev"
pub fn eo__24eo_5fprog_5fseq_2drev_2drev(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2drev_2drev(s, a0);
s.leave();
result
}
pub(super) fn case_567_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5frev_5frev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fseq_2drev_2drev(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_141_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_564_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_565_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_566_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_567_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fseq_2drev_2dconcat(s: &mut Store, v23: Term, a1: Term, v21: Term, v20: Term, v19: Term, a2: Term, v18: Term, v14: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListSingletonElim, &[v21, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v20, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5ftypeof(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5fnil(s, v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v27, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v18, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v14, v34) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v35))
}
pub(super) fn more_0_eo__24eo_5fprog_5fseq_2drev_2dconcat(s: &mut Store, v3: Term, v11: Term, v1: Term, v0: Term, a2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v3, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v1, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v0, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fseq_2drev_2dconcat(s, v23, a1, v21, v20, v19, a2, v18, v14)
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2drev_2dconcat(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fnil(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_list(EvalOp::ListConcat, &[v4, a1, v10]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fseq_2drev_2dconcat(s, v3, v11, v1, v0, a2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2drev_2dconcat(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2drev_2dconcat(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-rev-concat"
pub fn eo__24eo_5fprog_5fseq_2drev_2dconcat(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2drev_2dconcat(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_568_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5frev_5fconcat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fprog_5fseq_2drev_2dconcat(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s, a0, a1, a2, v14)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-repl-self-emp"
pub fn eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_189_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_569_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_189_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s: &mut Store, v27: Term, a0: Term, a1: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v25, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s: &mut Store, v4: Term, v16: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s, v27, a0, a1, v26, v25)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s, v4, v16, a0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-repl-no-change"
pub fn eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_190_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_570_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_190_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s: &mut Store, v27: Term, a0: Term, a1: Term, v26: Term, a2: Term, v25: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v31, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v30, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v25, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s: &mut Store, v15: Term, a2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v15 != a2 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s, v27, a0, a1, v26, a2, v25)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s, v15, a2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-repl-tgt-eq-len"
pub fn eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_191_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_571_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_191_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn cases_0_142_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_568_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_569_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_570_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_571_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s: &mut Store, a0: Term, a1: Term, a2: Term, v29: Term, v28: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v29, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v40))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s: &mut Store, v15: Term, a1: Term, a0: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v26 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a1 { return Ok(None); }
let v27 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v27 { return Ok(None); }
let v28 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s, a0, a1, a2, v29, v28)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s, v15, a1, a0, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-repl-len-one-emp-prefix"
pub fn eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_192_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_572_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_192_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s: &mut Store, v39: Term, v54: Term) -> CheckResult<Option<Term>> {
let v55 = match s.apply(v39, v54) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v55))
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s: &mut Store, v42: Term, a3: Term, v40: Term, a1: Term, v39: Term) -> CheckResult<Option<Term>> {
let v43 = match s.apply(v42, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v46, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v45, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v51, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v44, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s, v39, v54)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v32, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v31, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s, v42, a3, v40, a1, v39)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s: &mut Store, v15: Term, a2: Term, a3: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a2 { return Ok(None); }
if v25 != a3 { return Ok(None); }
let v30 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v30 { return Ok(None); }
more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s, a0, a1, a2, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a3 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s, v15, a2, a3, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-repl-emp-tgt-nemp"
pub fn eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_193_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_573_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_193_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s: &mut Store, v42: Term, a3: Term, v40: Term, a1: Term, a2: Term, v39: Term) -> CheckResult<Option<Term>> {
let v43 = match s.apply(v42, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v45, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v44, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v39, v52) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v53))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s: &mut Store, a3: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v32, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v31, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s, v42, a3, v40, a1, a2, v39)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s: &mut Store, v15: Term, a2: Term, a3: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a2 { return Ok(None); }
if v25 != a3 { return Ok(None); }
let v30 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v30 { return Ok(None); }
more_1_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s, a3, a0, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a3 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s, v15, a2, a3, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-repl-nemp-src-emp"
pub fn eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_194_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_574_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_194_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s: &mut Store, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s, v8, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-repl-self-src"
pub fn eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s, a0, a1);
s.leave();
result
}
pub(super) fn case_575_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_143_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_572_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_573_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_574_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_575_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_35_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_140_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_141_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_142_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_143_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_8_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_32_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_33_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_34_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_35_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2dlen_2dunit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2dlen_2dunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2dlen_2dunit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-len-unit"
pub fn eo__24eo_5fprog_5fseq_2dlen_2dunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2dlen_2dunit(s, a0);
s.leave();
result
}
pub(super) fn case_576_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5flen_5funit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fseq_2dlen_2dunit(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2dnth_2dunit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2dnth_2dunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2dnth_2dunit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-nth-unit"
pub fn eo__24eo_5fprog_5fseq_2dnth_2dunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2dnth_2dunit(s, a0);
s.leave();
result
}
pub(super) fn case_577_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5fnth_5funit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fseq_2dnth_2dunit(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v1, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-nth-concat-unit"
pub fn eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit(s, a0, a1);
s.leave();
result
}
pub(super) fn case_578_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_3_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s: &mut Store, v46: Term, v59: Term, a2: Term) -> CheckResult<Option<Term>> {
let v60 = match s.apply(v46, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v61))
}
pub(super) fn more_2_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s: &mut Store, a0: Term, a2: Term, a3: Term, a1: Term, v47: Term, a4: Term, v46: Term) -> CheckResult<Option<Term>> {
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v51, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.builtin_list(EvalOp::ListConcat, &[v50, a1, v55]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v49, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v47, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s, v46, v59, a2)
}
pub(super) fn more_1_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s: &mut Store, v35: Term, v36: Term, a0: Term, v29: Term, a4: Term, a2: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
let v37 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a0 { return Ok(None); }
let v38 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a4 { return Ok(None); }
let v45 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v45 { return Ok(None); }
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s, a0, a2, a3, a1, v47, a4, v46)
}
pub(super) fn more_0_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s: &mut Store, v18: Term, a0: Term, v15: Term, a1: Term, v4: Term, a4: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a0 { return Ok(None); }
if v22 != a1 { return Ok(None); }
let v27 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
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
more_1_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s, v35, v36, a0, v29, a4, a2, a3, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s, v18, a0, v15, a1, v4, a4, a2, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-nth-concat-unit-gen"
pub fn eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_195_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5fseq_2dnth_2dconcat_2dunit_2dgen(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_579_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v20 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v20 { return Ok(None); }
more_195_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn cases_0_144_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_576_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_577_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_578_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_579_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2drev_2dunit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2drev_2dunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2drev_2dunit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-rev-unit"
pub fn eo__24eo_5fprog_5fseq_2drev_2dunit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2drev_2dunit(s, a0);
s.leave();
result
}
pub(super) fn case_580_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5frev_5funit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fseq_2drev_2dunit(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2din_2dempty(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5fre_2din_2dempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2din_2dempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-in-empty"
pub fn eo__24eo_5fprog_5fre_2din_2dempty(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2din_2dempty(s, a0);
s.leave();
result
}
pub(super) fn case_581_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fin_5fempty, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2din_2dempty(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2din_2dsigma(s: &mut Store, v5: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v5, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2din_2dsigma(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2din_2dsigma(s, v5, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2din_2dsigma(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2din_2dsigma(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-in-sigma"
pub fn eo__24eo_5fprog_5fre_2din_2dsigma(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2din_2dsigma(s, a0);
s.leave();
result
}
pub(super) fn case_582_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fin_5fsigma, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2din_2dsigma(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-in-sigma-star"
pub fn eo__24eo_5fprog_5fre_2din_2dsigma_2dstar(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar(s, a0);
s.leave();
result
}
pub(super) fn case_583_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fin_5fsigma_5fstar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2din_2dsigma_2dstar(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_145_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_580_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_581_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_582_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_583_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2din_2dcstring(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fre_2din_2dcstring(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2din_2dcstring(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-in-cstring"
pub fn eo__24eo_5fprog_5fre_2din_2dcstring(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2din_2dcstring(s, a0, a1);
s.leave();
result
}
pub(super) fn case_584_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fin_5fcstring, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fre_2din_2dcstring(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_2din_2dcomp(s: &mut Store, v6: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v6, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2din_2dcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_2din_2dcomp(s, v6, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2din_2dcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2din_2dcomp(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-in-comp"
pub fn eo__24eo_5fprog_5fre_2din_2dcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2din_2dcomp(s, a0, a1);
s.leave();
result
}
pub(super) fn case_585_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fin_5fcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fre_2din_2dcomp(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s: &mut Store, v18: Term, v23: Term, v16: Term, v15: Term, v10: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v16, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v15, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v10, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s: &mut Store, a0: Term, a1: Term, v11: Term, a2: Term, a3: Term, v10: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListSingletonElim, &[v19, v22]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s, v18, v23, v16, v15, v10)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s, a0, a1, v11, a2, a3, v10)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-union-elim"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_586_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fstr_2din_2dre_2dunion_2delim(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s: &mut Store, v18: Term, v23: Term, v16: Term, v15: Term, v10: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v16, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v15, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v10, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s: &mut Store, a0: Term, a1: Term, v11: Term, a2: Term, a3: Term, v10: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListSingletonElim, &[v19, v22]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s, v18, v23, v16, v15, v10)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s, a0, a1, v11, a2, a3, v10)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-inter-elim"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_587_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_146_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_584_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_585_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_586_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_587_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s: &mut Store, v53: Term, v44: Term, v35: Term) -> CheckResult<Option<Term>> {
let v54 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v53, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v44, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v35, v56) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v57))
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s: &mut Store, v41: Term, a0: Term, v40: Term, v36: Term, a2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v42 = match s.apply(v41, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v36, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v45, v52) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s, v53, v44, v35)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s: &mut Store, v29: Term, a0: Term, a1: Term, a2: Term, v28: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v29, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v28, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v37, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s, v41, a0, v40, v36, a2, v35)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s: &mut Store, v15: Term, a2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v26 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a2 { return Ok(None); }
let v27 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v27 { return Ok(None); }
let v28 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s, v29, a0, a1, a2, v28)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s, v15, a2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-range-elim"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_196_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fstr_2din_2dre_2drange_2delim(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_588_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_196_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s: &mut Store, v0: Term, v23: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v0, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s: &mut Store, v11: Term, v7: Term, v2: Term, v0: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v12, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v11, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v7, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v2, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s, v0, v23, a0, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s, v11, v7, v2, v0, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-contains"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s, a0, a1);
s.leave();
result
}
pub(super) fn case_589_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5fcontains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fstr_2din_2dre_2dcontains(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s: &mut Store, v39: Term, v38: Term, v29: Term, v22: Term, v18: Term) -> CheckResult<Option<Term>> {
let v40 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v38, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v29, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v22, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v18, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s: &mut Store, v26: Term, v27: Term, v23: Term, v22: Term, v18: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v23, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Str(EoString::from_code_points(vec![48,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Str(EoString::from_code_points(vec![57,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v31, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v30, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s, v39, v38, v29, v22, v18)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s: &mut Store, v4: Term, a0: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Str(EoString::from_code_points(vec![48,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Str(EoString::from_code_points(vec![57,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s, v26, v27, v23, v22, v18)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s, v4, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-from-int-nemp-dig-range"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s, a0, a1);
s.leave();
result
}
pub(super) fn case_590_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s: &mut Store, v4: Term, v11: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v4, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Str(EoString::from_code_points(vec![48,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Str(EoString::from_code_points(vec![57,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s, v4, v11, v0)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-from-int-dig-range"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s, a0);
s.leave();
result
}
pub(super) fn case_591_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_147_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_588_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_589_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_590_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_591_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_36_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_144_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_145_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_146_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_147_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5feq_2drefl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5feq_2drefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5feq_2drefl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_eq-refl"
pub fn eo__24eo_5fprog_5feq_2drefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5feq_2drefl(s, a0);
s.leave();
result
}
pub(super) fn case_592_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eeq_5frefl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5feq_2drefl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5feq_2dsymm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5feq_2dsymm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5feq_2dsymm(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_eq-symm"
pub fn eo__24eo_5fprog_5feq_2dsymm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5feq_2dsymm(s, a0, a1);
s.leave();
result
}
pub(super) fn case_593_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eeq_5fsymm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5feq_2dsymm(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_2_eo__24eo_5fprog_5feq_2dcond_2ddeq(s: &mut Store, v36: Term, v39: Term, v35: Term, v34: Term, v27: Term) -> CheckResult<Option<Term>> {
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v35, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v34, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v27, v44) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v45))
}
pub(super) fn more_1_eo__24eo_5fprog_5feq_2dcond_2ddeq(s: &mut Store, a0: Term, a1: Term, a2: Term, v27: Term) -> CheckResult<Option<Term>> {
let v28 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v28, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5feq_2dcond_2ddeq(s, v36, v39, v35, v34, v27)
}
pub(super) fn more_0_eo__24eo_5fprog_5feq_2dcond_2ddeq(s: &mut Store, v4: Term, v16: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5feq_2dcond_2ddeq(s, a0, a1, a2, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5feq_2dcond_2ddeq(s, v4, v16, a0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5feq_2dcond_2ddeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_eq-cond-deq"
pub fn eo__24eo_5fprog_5feq_2dcond_2ddeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5feq_2dcond_2ddeq(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_197_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5feq_2dcond_2ddeq(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_594_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eeq_5fcond_5fdeq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_197_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5feq_2dite_2dlift(s: &mut Store, v11: Term, a1: Term, a3: Term, v10: Term, a2: Term, v8: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v8, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5feq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5feq_2dite_2dlift(s, v11, a1, a3, v10, a2, v8)
}
pub(super) fn body_eo__24eo_5fprog_5feq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5feq_2dite_2dlift(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_eq-ite-lift"
pub fn eo__24eo_5fprog_5feq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5feq_2dite_2dlift(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_595_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eeq_5fite_5flift, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5feq_2dite_2dlift(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_148_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_592_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_593_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_594_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_595_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s: &mut Store, v0: Term, v11: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v0, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v12, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fnil(s, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v3, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v1, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s, v0, v11, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_distinct-binary-elim"
pub fn eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_596_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edistinct_5fbinary_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fdistinct_2dbinary_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s: &mut Store, a1: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
if v4 != a0 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s, a1, v14, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-bv2nat-int2bv"
pub fn eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_597_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fbv2nat_5fint2bv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s: &mut Store, v41: Term, v45: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v46 = match s.apply(v41, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v48, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v47, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v53, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v51, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v46, v56) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v57))
}
pub(super) fn more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a0 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a1 { return Ok(None); }
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v42, v44) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s, v41, v45, a2, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s: &mut Store, v17: Term, v19: Term, v18: Term, a1: Term, v4: Term, a4: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a1 { return Ok(None); }
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
if v28 != a2 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s, v34, v35, a0, v32, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a0 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s, v17, v19, v18, a1, v4, a4, a2, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-bv2nat-int2bv-extend"
pub fn eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_198_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_598_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_198_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s: &mut Store, a2: Term, v44: Term, a1: Term, v43: Term) -> CheckResult<Option<Term>> {
let v45 = match s.construct(Constructor::eo_extract, &[a2, v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v43, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s: &mut Store, v34: Term, v35: Term, a0: Term, v32: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a0 { return Ok(None); }
let v37 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v37 { return Ok(None); }
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v38, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s, a2, v44, a1, v43)
}
pub(super) fn more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s: &mut Store, v17: Term, v19: Term, v18: Term, a1: Term, v4: Term, a4: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a1 { return Ok(None); }
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
if v28 != a2 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s, v34, v35, a0, v32, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a0 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s, v17, v19, v18, a1, v4, a4, a2, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-bv2nat-int2bv-extract"
pub fn eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_199_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_599_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_199_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn cases_0_149_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_596_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_597_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_598_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_599_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-int2bv-bv2nat"
pub fn eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat(s, a0, a1);
s.leave();
result
}
pub(super) fn case_600_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fint2bv_5fbv2nat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s: &mut Store, a2: Term, a1: Term, v38: Term, v36: Term, v28: Term, v19: Term) -> CheckResult<Option<Term>> {
let v39 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v36, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v28, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v19, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v44))
}
pub(super) fn more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s: &mut Store, v26: Term, a1: Term, a0: Term, a2: Term, v19: Term) -> CheckResult<Option<Term>> {
let v27 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v29, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_bvuge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s, a2, a1, v38, v36, v28, v19)
}
pub(super) fn more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s: &mut Store, a0: Term, v14: Term, a1: Term, v13: Term, a2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v13, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v20, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s, v26, a1, a0, a2, v19)
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s, a0, v14, a1, v13, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-bv2nat-geq-elim"
pub fn eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_200_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_601_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_200_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s: &mut Store, v4: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v4, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s, v4, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-int2bv-bvult-equiv"
pub fn eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s, a0, a1);
s.leave();
result
}
pub(super) fn case_602_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s: &mut Store, v4: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v4, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s, v4, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-int2bv-bvule-equiv"
pub fn eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s, a0, a1);
s.leave();
result
}
pub(super) fn case_603_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_150_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_600_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_601_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_602_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_603_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_3_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s: &mut Store, a0: Term, v56: Term, a2: Term, v55: Term, v41: Term) -> CheckResult<Option<Term>> {
let v57 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v55, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v41, v61) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v62))
}
pub(super) fn more_2_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s: &mut Store, v44: Term, a0: Term, v43: Term, v42: Term, a2: Term, v41: Term) -> CheckResult<Option<Term>> {
let v45 = match s.apply(v44, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v47]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v48, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v46, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v42, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v52, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s, a0, v56, a2, v55, v41)
}
pub(super) fn more_1_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s: &mut Store, v31: Term, v33: Term, v32: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v31 != v33 { return Ok(None); }
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a0 { return Ok(None); }
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_sbv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_extract, &[a1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s, v44, a0, v43, v42, a2, v41)
}
pub(super) fn more_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a4: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
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
if v28 != a2 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s, v31, v33, v32, a0, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s, v17, v19, v18, a0, v11, a4, a2, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_uf-sbv-to-int-elim"
pub fn eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_201_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_604_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_201_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_6_eo__24run_5fevaluate(s: &mut Store, v12: Term, v14: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.builtin_core(EvalOp::Add, &[v12, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::ToRat, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v18 = match s.literal(Lit::Rational(v17)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Eq, &[v16, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Or, &[v11, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn more_7_eo__24run_5fevaluate(s: &mut Store, v12: Term, v14: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.builtin_core(EvalOp::Add, &[v12, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::ToRat, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v18 = match s.literal(Lit::Rational(v17)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Eq, &[v16, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Or, &[v11, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn more_20_eo__24run_5fevaluate(s: &mut Store, v10: Term, v11: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match s.builtin_core(EvalOp::Extract, &[v10, v11, v16]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn more_22_eo__24run_5fevaluate(s: &mut Store, v28: Term, v40: Term) -> CheckResult<Term> {
let v41 = match s.builtin_core(EvalOp::Concat, &[v28, v40]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
pub(super) fn case_0_eo__24str_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_0_eo__24str_5fis_5fprefix_5fflat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_1_eo__24str_5fis_5fprefix_5fflat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
pub(super) fn case_2_eo__24str_5fis_5fprefix_5fflat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v14)))
}
pub(super) fn case_3_eo__24str_5fis_5fprefix_5fflat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24str_5fis_5fprefix_5fflat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fis_5fprefix_5fflat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fis_5fprefix_5fflat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fis_5fprefix_5fflat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24str_5fis_5fprefix_5fflat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5fis_5fprefix_5fflat(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fis_5fprefix_5fflat(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$str_is_prefix_flat"
pub fn eo__24str_5fis_5fprefix_5fflat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1051), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fis_5fprefix_5fflat(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1051), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_2_eo__24str_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Add, &[a3, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, a1, a2, v8, a4])))
}
// EO program "$str_eval_replace_all_rec"
pub fn eo__24str_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(1037), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1037), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5feval_5freplace_5fall_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) {
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
pub(super) fn step_eo__24str_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Next<[Term; 5]>> {
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
if let Some(found) = match case_0_eo__24str_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24str_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5fis_5fprefix_5fflat(s, v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_0_eo__24str_5feval_5freplace_5fall_5frec(s, v11, a4, v2, a1, a2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v19)))
}
pub(super) fn if_0_eo__24str_5feval_5freplace_5fall_5frec(s: &mut Store, condition: Term, a4: Term, v2: Term, a1: Term, a2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[a4, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24str_5feval_5freplace_5fall_5frec(s, v2, a1, a2, v13, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Concat, &[a2, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24str_5feval_5freplace_5fall_5frec(s, v2, a1, a2, v16, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Concat, &[v5, v17]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_24_eo__24run_5fevaluate(s: &mut Store, condition: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v8)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v17, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5fflatten(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v20, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fflatten(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24str_5feval_5freplace_5fall_5frec(s, v19, v22, v2, v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_25_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term, v8: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Eq, &[v5, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_24_eo__24run_5fevaluate(s, v16, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
Some(false) => {
let v27 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_34_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.builtin_core(EvalOp::IsStr, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IsStr, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::And, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::IsStr, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::And, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match if_25_eo__24run_5fevaluate(s, v14, v5, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_26_eo__24run_5fevaluate(s: &mut Store, v7: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.builtin_core(EvalOp::Eq, &[v7, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn if_36_eo__24run_5fevaluate(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.builtin_core(EvalOp::ToString, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5fto_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a2))
}
// EO program "$str_to_int_eval_rec"
pub fn eo__24str_5fto_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1074), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fto_5fint_5feval_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1074), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fto_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fto_5fint_5feval_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fto_5fint_5feval_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fto_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(48u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Gt, &[v7, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(48u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5fto_5fint_5feval_5frec(s, v14, v11, a1, v5, a2, v2)
}
pub(super) fn if_0_eo__24str_5fto_5fint_5feval_5frec(s: &mut Store, condition: Term, a1: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Mul, &[a1, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(48u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Add, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Mul, &[v22, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::Add, &[v23, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24str_5fto_5fint_5feval_5frec(s, v2, v19, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
Some(false) => {
let v26 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24str_5fto_5fint_5feval_5frec(s: &mut Store, v14: Term, v11: Term, a1: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Not, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::And, &[v11, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_0_eo__24str_5fto_5fint_5feval_5frec(s, v17, a1, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn if_0_eo__24str_5ffrom_5fint_5feval_5frec(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.literal(Lit::Str(EoString::from_code_points(vec![48,]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
Ok(a2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5ffrom_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::Eq, &[a2, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match if_0_eo__24str_5ffrom_5fint_5feval_5frec(s, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_1_eo__24str_5ffrom_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::IntDiv, &[a1, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::IntMod, &[a1, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::ToString, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Concat, &[v13, a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v8, v14])))
}
pub(super) fn step_eo__24str_5ffrom_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5ffrom_5fint_5feval_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5ffrom_5fint_5feval_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5ffrom_5fint_5feval_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5ffrom_5fint_5feval_5frec(s, a0, a1, a2) {
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
// EO program "$str_from_int_eval_rec"
pub fn eo__24str_5ffrom_5fint_5feval_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1046), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5ffrom_5fint_5feval_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1046), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24str_5fleq_5feval_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24str_5fleq_5feval_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$str_leq_eval_rec"
pub fn eo__24str_5fleq_5feval_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1052), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fleq_5feval_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1052), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fleq_5feval_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fleq_5feval_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fleq_5feval_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fleq_5feval_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fleq_5feval_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.builtin_core(EvalOp::Eq, &[v5, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_0_eo__24str_5fleq_5feval_5frec(s, v14, v2, v9, v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn if_0_eo__24str_5fleq_5feval_5frec(s: &mut Store, condition: Term, v2: Term, v9: Term, v12: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match eo__24str_5fleq_5feval_5frec(s, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.builtin_core(EvalOp::ToInt, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Gt, &[v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24str_5fcase_5fconv_5frec(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(32u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5fcase_5fconv_5frec(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(32u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24str_5fcase_5fconv_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$str_case_conv_rec"
pub fn eo__24str_5fcase_5fconv_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1034), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fcase_5fconv_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1034), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fcase_5fconv_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fcase_5fconv_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fcase_5fconv_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fcase_5fconv_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fcase_5fconv_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v7 { return Ok(None); }
let v8 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(91u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Gt, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(64u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5fcase_5fconv_5frec(s, v12, v13, v11, v8, v2)
}
pub(super) fn case_1_eo__24str_5fcase_5fconv_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v7 { return Ok(None); }
let v8 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(123u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Gt, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(96u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24str_5fcase_5fconv_5frec(s, v12, v13, v11, v8, v2)
}
pub(super) fn more_1_eo__24str_5fcase_5fconv_5frec(s: &mut Store, v12: Term, v13: Term, v11: Term, v8: Term, v2: Term) -> CheckResult<Option<Term>> {
let v14 = match s.builtin_core(EvalOp::Gt, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::And, &[v11, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_0_eo__24str_5fcase_5fconv_5frec(s, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Add, &[v8, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::ToString, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fcase_5fconv_5frec(s, v2, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Concat, &[v20, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn more_3_eo__24str_5fcase_5fconv_5frec(s: &mut Store, v12: Term, v13: Term, v11: Term, v8: Term, v2: Term) -> CheckResult<Option<Term>> {
let v14 = match s.builtin_core(EvalOp::Gt, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::And, &[v11, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_2_eo__24str_5fcase_5fconv_5frec(s, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::Add, &[v8, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::ToString, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fcase_5fconv_5frec(s, v2, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Concat, &[v20, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn more_48_eo__24run_5fevaluate(s: &mut Store, v36: Term, v40: Term, v42: Term, v35: Term) -> CheckResult<Term> {
let v43 = match s.builtin_core(EvalOp::Extract, &[v36, v40, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_core(EvalOp::Concat, &[v35, v43]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
pub(super) fn if_51_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24bv_5fbitwidth(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Pow, &[v20, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_52_eo__24run_5fevaluate(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24bv_5fbitwidth(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match if_51_eo__24run_5fevaluate(s, v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24bv_5fbitwidth(s, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_57_eo__24run_5fevaluate(s: &mut Store, v54: Term, v51: Term, v52: Term, v50: Term) -> CheckResult<Term> {
let v55 = match eo__24bv_5fbitwidth(s, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_core(EvalOp::Add, &[v55, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.builtin_core(EvalOp::Extract, &[v51, v52, v57]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_core(EvalOp::ToInt, &[v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_core(EvalOp::Add, &[v50, v59]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
pub(super) fn more_61_eo__24run_5fevaluate(s: &mut Store, v118: Term, v115: Term, v116: Term, v114: Term) -> CheckResult<Term> {
let v119 = match eo__24bv_5fbitwidth(s, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.builtin_core(EvalOp::Add, &[v119, v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_core(EvalOp::Extract, &[v115, v116, v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_core(EvalOp::ToInt, &[v122]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_core(EvalOp::Add, &[v114, v123]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v124)
}
pub(super) fn more_67_eo__24run_5fevaluate(s: &mut Store, v54: Term, v51: Term, v52: Term, v50: Term) -> CheckResult<Term> {
let v55 = match eo__24bv_5fbitwidth(s, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_core(EvalOp::Add, &[v55, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.builtin_core(EvalOp::Extract, &[v51, v52, v57]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_core(EvalOp::ToInt, &[v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_core(EvalOp::Add, &[v50, v59]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
pub(super) fn more_71_eo__24run_5fevaluate(s: &mut Store, v118: Term, v115: Term, v116: Term, v114: Term) -> CheckResult<Term> {
let v119 = match eo__24bv_5fbitwidth(s, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.builtin_core(EvalOp::Add, &[v119, v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_core(EvalOp::Extract, &[v115, v116, v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_core(EvalOp::ToInt, &[v122]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_core(EvalOp::Add, &[v114, v123]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v124)
}
pub(super) fn more_75_eo__24run_5fevaluate(s: &mut Store, v183: Term, v180: Term, v181: Term, v179: Term) -> CheckResult<Term> {
let v184 = match eo__24bv_5fbitwidth(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.builtin_core(EvalOp::Add, &[v184, v185]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.builtin_core(EvalOp::Extract, &[v180, v181, v186]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.builtin_core(EvalOp::ToInt, &[v187]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_core(EvalOp::Add, &[v179, v188]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v189)
}
pub(super) fn more_79_eo__24run_5fevaluate(s: &mut Store, v247: Term, v244: Term, v245: Term, v243: Term) -> CheckResult<Term> {
let v248 = match eo__24bv_5fbitwidth(s, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.builtin_core(EvalOp::Add, &[v248, v249]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.builtin_core(EvalOp::Extract, &[v244, v245, v250]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.builtin_core(EvalOp::ToInt, &[v251]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.builtin_core(EvalOp::Add, &[v243, v252]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v253)
}
pub(super) fn more_88_eo__24run_5fevaluate(s: &mut Store, v54: Term, v51: Term, v52: Term, v50: Term) -> CheckResult<Term> {
let v55 = match eo__24bv_5fbitwidth(s, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_core(EvalOp::Add, &[v55, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.builtin_core(EvalOp::Extract, &[v51, v52, v57]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_core(EvalOp::ToInt, &[v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_core(EvalOp::Add, &[v50, v59]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
pub(super) fn more_92_eo__24run_5fevaluate(s: &mut Store, v118: Term, v115: Term, v116: Term, v114: Term) -> CheckResult<Term> {
let v119 = match eo__24bv_5fbitwidth(s, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.builtin_core(EvalOp::Add, &[v119, v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_core(EvalOp::Extract, &[v115, v116, v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_core(EvalOp::ToInt, &[v122]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_core(EvalOp::Add, &[v114, v123]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v124)
}
pub(super) fn more_98_eo__24run_5fevaluate(s: &mut Store, v54: Term, v51: Term, v52: Term, v50: Term) -> CheckResult<Term> {
let v55 = match eo__24bv_5fbitwidth(s, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_core(EvalOp::Add, &[v55, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.builtin_core(EvalOp::Extract, &[v51, v52, v57]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_core(EvalOp::ToInt, &[v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_core(EvalOp::Add, &[v50, v59]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
pub(super) fn more_102_eo__24run_5fevaluate(s: &mut Store, v118: Term, v115: Term, v116: Term, v114: Term) -> CheckResult<Term> {
let v119 = match eo__24bv_5fbitwidth(s, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.builtin_core(EvalOp::Add, &[v119, v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_core(EvalOp::Extract, &[v115, v116, v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_core(EvalOp::ToInt, &[v122]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_core(EvalOp::Add, &[v114, v123]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v124)
}
pub(super) fn more_106_eo__24run_5fevaluate(s: &mut Store, v183: Term, v180: Term, v181: Term, v179: Term) -> CheckResult<Term> {
let v184 = match eo__24bv_5fbitwidth(s, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.builtin_core(EvalOp::Add, &[v184, v185]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.builtin_core(EvalOp::Extract, &[v180, v181, v186]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.builtin_core(EvalOp::ToInt, &[v187]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_core(EvalOp::Add, &[v179, v188]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v189)
}
pub(super) fn more_110_eo__24run_5fevaluate(s: &mut Store, v247: Term, v244: Term, v245: Term, v243: Term) -> CheckResult<Term> {
let v248 = match eo__24bv_5fbitwidth(s, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.builtin_core(EvalOp::Add, &[v248, v249]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.builtin_core(EvalOp::Extract, &[v244, v245, v250]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.builtin_core(EvalOp::ToInt, &[v251]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.builtin_core(EvalOp::Add, &[v243, v252]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v253)
}
pub(super) fn more_125_eo__24run_5fevaluate(s: &mut Store, v56: Term, v53: Term, v54: Term, v52: Term) -> CheckResult<Term> {
let v57 = match eo__24bv_5fbitwidth(s, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_core(EvalOp::Add, &[v57, v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_core(EvalOp::Extract, &[v53, v54, v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.builtin_core(EvalOp::ToInt, &[v60]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.builtin_core(EvalOp::Add, &[v52, v61]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
pub(super) fn more_134_eo__24run_5fevaluate(s: &mut Store, v57: Term, v54: Term, v55: Term, v53: Term) -> CheckResult<Term> {
let v58 = match eo__24bv_5fbitwidth(s, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_core(EvalOp::Add, &[v58, v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.builtin_core(EvalOp::Extract, &[v54, v55, v60]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.builtin_core(EvalOp::ToInt, &[v61]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.builtin_core(EvalOp::Add, &[v53, v62]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v63)
}
pub(super) fn case_73_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24bv_5fbitwidth(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_77_eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
Ok(Some(a0))
}
// EO program "$run_evaluate"
pub fn eo__24run_5fevaluate(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(958), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24run_5fevaluate(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(958), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn case_605_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_606_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
match s.cached_program(ProgramId(878), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24get_5fai_5fnorm_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(878), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
