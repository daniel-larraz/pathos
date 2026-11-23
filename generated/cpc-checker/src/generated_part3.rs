//! Generated functions, module 3 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn more_25_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v228: Term, v205: Term, v180: Term, v179: Term, a0: Term, v7: Term, v4: Term, v178: Term) -> CheckResult<Term> {
let v229 = match eo__24eo_5ftypeof(s, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match eo__24seq_5fempty(s, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v205, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v180, v231) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v179, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match if_21_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24eo_5fprog_5fconcat_5flprop(s, v238, v245, v246, a0, v4, v237, v236, v235, v234, v233, v178)
}
pub(super) fn more_24_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v181: Term, v204: Term, a0: Term, v7: Term, v4: Term, v180: Term, v179: Term, v178: Term) -> CheckResult<Term> {
let v205 = match s.apply(v181, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match if_19_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.builtin_list(EvalOp::ListNth, &[v207, v214, v215]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match if_20_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_list(EvalOp::ListNth, &[v217, v224, v225]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match eo__24str_5funify_5fsplit(s, v216, v226, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v206, v227) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24eo_5fprog_5fconcat_5flprop(s, v228, v205, v180, v179, a0, v7, v4, v178)
}
pub(super) fn more_23_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, a0: Term, v7: Term, v4: Term, v180: Term, v179: Term, v178: Term) -> CheckResult<Term> {
let v181 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match if_17_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.builtin_list(EvalOp::ListNth, &[v183, v190, v191]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match if_18_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.builtin_list(EvalOp::ListNth, &[v193, v200, v201]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match eo__24str_5funify_5fsplit(s, v192, v202, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v182, v203) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24eo_5fprog_5fconcat_5flprop(s, v181, v204, a0, v7, v4, v180, v179, v178)
}
pub(super) fn requires_28_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v45: Term, v24: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Term> {
if v45 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v45) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v46 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match if_2_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_list(EvalOp::ListNth, &[v48, v55, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v47, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match if_16_eo__24eo_5fprog_5fconcat_5flprop(s, a0, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v58, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v46, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7, v4, v180, v179, v178)
}
pub(super) fn requires_29_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v35: Term, v20: Term, a0: Term, v4: Term, v24: Term, v7: Term) -> CheckResult<Term> {
if v35 != v20 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v35) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match if_1_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_list(EvalOp::ListNth, &[v36, v43, v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match requires_28_eo__24eo_5fprog_5fconcat_5flprop(s, v45, v24, a0, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v269)
}
pub(super) fn more_30_eo__24eo_5fprog_5fconcat_5flprop(s: &mut Store, v19: Term, v21: Term, v13: Term, a0: Term, v7: Term, v20: Term, v4: Term) -> CheckResult<Option<Term>> {
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match if_0_eo__24eo_5fprog_5fconcat_5flprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_list(EvalOp::ListNth, &[v26, v33, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match requires_29_eo__24eo_5fprog_5fconcat_5flprop(s, v35, v20, a0, v4, v24, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v270))
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
more_30_eo__24eo_5fprog_5fconcat_5flprop(s, v19, v21, v13, a0, v7, v20, v4)
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
pub(super) fn more_8_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5flprop(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
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
more_8_eo__24eo_5fcmd_5fstep_5fproven(s, v14, v2, v13)
}
pub(super) fn cases_0_23_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_92_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_93_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_94_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_95_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_5_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_20_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_21_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_22_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_23_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
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
pub(super) fn if_103_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1000 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1001 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1002 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1001, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1003 = match s.builtin_list(EvalOp::ListRev, &[v1000, v1002]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1003)
}
Some(false) => {
let v1004 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1005 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1004, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1005)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_104_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1016 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1017 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1018 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1017, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1019 = match s.builtin_list(EvalOp::ListRev, &[v1016, v1018]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1019)
}
Some(false) => {
let v1020 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1021 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1020, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1021)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_105_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1027 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1028 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1029 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1028, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1030 = match s.builtin_list(EvalOp::ListRev, &[v1027, v1029]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1030)
}
Some(false) => {
let v1031 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1032 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1031, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1032)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_106_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1041 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1042 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1043 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1042, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1044 = match s.builtin_list(EvalOp::ListRev, &[v1041, v1043]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1044)
}
Some(false) => {
let v1045 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1046 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1045, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1046)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_107_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1052 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1053 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1054 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1053, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1055 = match s.builtin_list(EvalOp::ListRev, &[v1052, v1054]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1055)
}
Some(false) => {
let v1056 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1057 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1056, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1057)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_108_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1024: Term, v1025: Term, v1038: Term) -> CheckResult<Term> {
let v1039 = match s.builtin_core(EvalOp::Extract, &[v1024, v1025, v1038]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1039)
}
pub(super) fn if_109_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1015 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1022 = match if_104_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1023 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1024 = match s.builtin_list(EvalOp::ListNth, &[v1015, v1022, v1023]) { Ok(v) => v, Err(e) => return Err(e) };
let v1025 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1026 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1033 = match if_105_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1034 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1035 = match s.builtin_list(EvalOp::ListNth, &[v1026, v1033, v1034]) { Ok(v) => v, Err(e) => return Err(e) };
let v1036 = match s.builtin_core(EvalOp::Length, &[v1035]) { Ok(v) => v, Err(e) => return Err(e) };
let v1037 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1038 = match s.builtin_core(EvalOp::Add, &[v1036, v1037]) { Ok(v) => v, Err(e) => return Err(e) };
more_108_eo__24eo_5fprog_5fconcat_5fcprop(s, v1024, v1025, v1038)
}
Some(false) => {
let v1040 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1047 = match if_106_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1048 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1049 = match s.builtin_list(EvalOp::ListNth, &[v1040, v1047, v1048]) { Ok(v) => v, Err(e) => return Err(e) };
let v1050 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1051 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1058 = match if_107_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1059 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1060 = match s.builtin_list(EvalOp::ListNth, &[v1051, v1058, v1059]) { Ok(v) => v, Err(e) => return Err(e) };
let v1061 = match s.builtin_core(EvalOp::Length, &[v1060]) { Ok(v) => v, Err(e) => return Err(e) };
let v1062 = match s.builtin_core(EvalOp::Extract, &[v1049, v1050, v1061]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1062)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_110_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1069 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1070 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1071 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1070, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1072 = match s.builtin_list(EvalOp::ListRev, &[v1069, v1071]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1072)
}
Some(false) => {
let v1073 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1074 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1073, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1074)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_111_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1080 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1081 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1082 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1081, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1083 = match s.builtin_list(EvalOp::ListRev, &[v1080, v1082]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1083)
}
Some(false) => {
let v1084 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1085 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1084, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1085)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_112_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1094 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1095 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1096 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1095, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1097 = match s.builtin_list(EvalOp::ListRev, &[v1094, v1096]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1097)
}
Some(false) => {
let v1098 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1099 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1098, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1099)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_113_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1105 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1106 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1107 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1106, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1108 = match s.builtin_list(EvalOp::ListRev, &[v1105, v1107]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1108)
}
Some(false) => {
let v1109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1110 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1109, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1110)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_114_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1077: Term, v1078: Term, v1091: Term) -> CheckResult<Term> {
let v1092 = match s.builtin_core(EvalOp::Extract, &[v1077, v1078, v1091]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1092)
}
pub(super) fn if_115_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1068 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1075 = match if_110_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1076 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1077 = match s.builtin_list(EvalOp::ListNth, &[v1068, v1075, v1076]) { Ok(v) => v, Err(e) => return Err(e) };
let v1078 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1079 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1086 = match if_111_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1087 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1088 = match s.builtin_list(EvalOp::ListNth, &[v1079, v1086, v1087]) { Ok(v) => v, Err(e) => return Err(e) };
let v1089 = match s.builtin_core(EvalOp::Length, &[v1088]) { Ok(v) => v, Err(e) => return Err(e) };
let v1090 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1091 = match s.builtin_core(EvalOp::Add, &[v1089, v1090]) { Ok(v) => v, Err(e) => return Err(e) };
more_114_eo__24eo_5fprog_5fconcat_5fcprop(s, v1077, v1078, v1091)
}
Some(false) => {
let v1093 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1100 = match if_112_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1101 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1102 = match s.builtin_list(EvalOp::ListNth, &[v1093, v1100, v1101]) { Ok(v) => v, Err(e) => return Err(e) };
let v1103 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1111 = match if_113_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1112 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1113 = match s.builtin_list(EvalOp::ListNth, &[v1104, v1111, v1112]) { Ok(v) => v, Err(e) => return Err(e) };
let v1114 = match s.builtin_core(EvalOp::Length, &[v1113]) { Ok(v) => v, Err(e) => return Err(e) };
let v1115 = match s.builtin_core(EvalOp::Extract, &[v1102, v1103, v1114]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1115)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24str_5fflatten(s: &mut Store, v10: Term, v11: Term, v5: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListRepeat, &[v12, v13, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24iota_5frec(s, v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
pub(super) fn case_0_eo__24str_5fflatten_5fword_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$str_flatten_word_rec"
pub fn eo__24str_5fflatten_5fword_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1061), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fflatten_5fword_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1061), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn requires_3_eo__24str_5fflatten(s: &mut Store, a0: Term, v1: Term) -> CheckResult<Term> {
if a0 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_2_eo__24str_5fflatten(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24seq_5fempty(s, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match requires_3_eo__24str_5fflatten(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
// EO program "$str_flatten"
pub fn eo__24str_5fflatten(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1060), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fflatten(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1060), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
more_0_eo__24str_5fflatten(s, v17, v2, v14)
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
let v26 = match if_2_eo__24str_5fflatten(s, v7, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn more_0_eo__24str_5fflatten(s: &mut Store, v17: Term, v2: Term, v14: Term) -> CheckResult<Option<Term>> {
let v18 = match eo__24str_5fflatten(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5fflatten(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListConcat, &[v14, v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn if_2_eo__24str_5fflatten(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match requires_1_eo__24str_5fflatten(s, v10, v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5fflatten_5fword_5frec(s, v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24str_5fflatten(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListConcat, &[v8, v19, v20]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
Some(false) => {
let v22 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24str_5fflatten(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_116_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1013 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1014 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1063 = match if_109_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1064 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1014, v1063]) { Ok(v) => v, Err(e) => return Err(e) };
let v1065 = match eo__24str_5fflatten(s, v1064) { Ok(v) => v, Err(e) => return Err(e) };
let v1066 = match s.builtin_list(EvalOp::ListRev, &[v1013, v1065]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1066)
}
Some(false) => {
let v1067 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1116 = match if_115_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1117 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1067, v1116]) { Ok(v) => v, Err(e) => return Err(e) };
let v1118 = match eo__24str_5fflatten(s, v1117) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1118)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_117_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1123 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1124 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1125 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1124, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1126 = match s.builtin_list(EvalOp::ListRev, &[v1123, v1125]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1126)
}
Some(false) => {
let v1127 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1128 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1127, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1128)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_118_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1137 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1138 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1139 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1138, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1140 = match s.builtin_list(EvalOp::ListRev, &[v1137, v1139]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1140)
}
Some(false) => {
let v1141 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1142 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1141, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1142)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_119_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1120 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1121 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1122 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1129 = match if_117_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1130 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1131 = match s.builtin_list(EvalOp::ListNth, &[v1122, v1129, v1130]) { Ok(v) => v, Err(e) => return Err(e) };
let v1132 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1121, v1131]) { Ok(v) => v, Err(e) => return Err(e) };
let v1133 = match eo__24str_5fflatten(s, v1132) { Ok(v) => v, Err(e) => return Err(e) };
let v1134 = match s.builtin_list(EvalOp::ListRev, &[v1120, v1133]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1134)
}
Some(false) => {
let v1135 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1136 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1143 = match if_118_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1144 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1145 = match s.builtin_list(EvalOp::ListNth, &[v1136, v1143, v1144]) { Ok(v) => v, Err(e) => return Err(e) };
let v1146 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1135, v1145]) { Ok(v) => v, Err(e) => return Err(e) };
let v1147 = match eo__24str_5fflatten(s, v1146) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1147)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_120_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
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
pub(super) fn if_121_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1176 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1177 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1178 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1177, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1179 = match s.builtin_list(EvalOp::ListRev, &[v1176, v1178]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1179)
}
Some(false) => {
let v1180 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1181 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1180, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1181)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_122_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1187 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1188 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1189 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1188, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1190 = match s.builtin_list(EvalOp::ListRev, &[v1187, v1189]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1190)
}
Some(false) => {
let v1191 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1192 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1191, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1192)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_123_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1201 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1202 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1203 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1202, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1204 = match s.builtin_list(EvalOp::ListRev, &[v1201, v1203]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1204)
}
Some(false) => {
let v1205 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1206 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1205, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1206)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_124_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1212 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1213 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1214 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1213, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1215 = match s.builtin_list(EvalOp::ListRev, &[v1212, v1214]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1215)
}
Some(false) => {
let v1216 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1217 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1216, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1217)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_125_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1184: Term, v1185: Term, v1198: Term) -> CheckResult<Term> {
let v1199 = match s.builtin_core(EvalOp::Extract, &[v1184, v1185, v1198]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1199)
}
pub(super) fn if_126_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1175 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1182 = match if_121_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1183 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1184 = match s.builtin_list(EvalOp::ListNth, &[v1175, v1182, v1183]) { Ok(v) => v, Err(e) => return Err(e) };
let v1185 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1186 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1193 = match if_122_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1194 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1195 = match s.builtin_list(EvalOp::ListNth, &[v1186, v1193, v1194]) { Ok(v) => v, Err(e) => return Err(e) };
let v1196 = match s.builtin_core(EvalOp::Length, &[v1195]) { Ok(v) => v, Err(e) => return Err(e) };
let v1197 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1198 = match s.builtin_core(EvalOp::Add, &[v1196, v1197]) { Ok(v) => v, Err(e) => return Err(e) };
more_125_eo__24eo_5fprog_5fconcat_5fcprop(s, v1184, v1185, v1198)
}
Some(false) => {
let v1200 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1207 = match if_123_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1208 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1209 = match s.builtin_list(EvalOp::ListNth, &[v1200, v1207, v1208]) { Ok(v) => v, Err(e) => return Err(e) };
let v1210 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1211 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1218 = match if_124_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1219 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1220 = match s.builtin_list(EvalOp::ListNth, &[v1211, v1218, v1219]) { Ok(v) => v, Err(e) => return Err(e) };
let v1221 = match s.builtin_core(EvalOp::Length, &[v1220]) { Ok(v) => v, Err(e) => return Err(e) };
let v1222 = match s.builtin_core(EvalOp::Extract, &[v1209, v1210, v1221]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1222)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_127_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1229 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1230 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1231 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1230, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1232 = match s.builtin_list(EvalOp::ListRev, &[v1229, v1231]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1232)
}
Some(false) => {
let v1233 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1234 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1233, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1234)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_128_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1240 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1241 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1242 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1241, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1243 = match s.builtin_list(EvalOp::ListRev, &[v1240, v1242]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1243)
}
Some(false) => {
let v1244 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1245 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1244, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1245)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_129_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1254 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1255 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1256 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1255, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1257 = match s.builtin_list(EvalOp::ListRev, &[v1254, v1256]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1257)
}
Some(false) => {
let v1258 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1259 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1258, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1259)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_130_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1265 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1266 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1267 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1266, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1268 = match s.builtin_list(EvalOp::ListRev, &[v1265, v1267]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1268)
}
Some(false) => {
let v1269 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1270 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1269, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1270)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_131_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1237: Term, v1238: Term, v1251: Term) -> CheckResult<Term> {
let v1252 = match s.builtin_core(EvalOp::Extract, &[v1237, v1238, v1251]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1252)
}
pub(super) fn if_132_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1228 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1235 = match if_127_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1236 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1237 = match s.builtin_list(EvalOp::ListNth, &[v1228, v1235, v1236]) { Ok(v) => v, Err(e) => return Err(e) };
let v1238 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1239 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1246 = match if_128_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1247 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1248 = match s.builtin_list(EvalOp::ListNth, &[v1239, v1246, v1247]) { Ok(v) => v, Err(e) => return Err(e) };
let v1249 = match s.builtin_core(EvalOp::Length, &[v1248]) { Ok(v) => v, Err(e) => return Err(e) };
let v1250 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1251 = match s.builtin_core(EvalOp::Add, &[v1249, v1250]) { Ok(v) => v, Err(e) => return Err(e) };
more_131_eo__24eo_5fprog_5fconcat_5fcprop(s, v1237, v1238, v1251)
}
Some(false) => {
let v1253 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1260 = match if_129_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1261 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1262 = match s.builtin_list(EvalOp::ListNth, &[v1253, v1260, v1261]) { Ok(v) => v, Err(e) => return Err(e) };
let v1263 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1264 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1271 = match if_130_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1272 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1273 = match s.builtin_list(EvalOp::ListNth, &[v1264, v1271, v1272]) { Ok(v) => v, Err(e) => return Err(e) };
let v1274 = match s.builtin_core(EvalOp::Length, &[v1273]) { Ok(v) => v, Err(e) => return Err(e) };
let v1275 = match s.builtin_core(EvalOp::Extract, &[v1262, v1263, v1274]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1275)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_133_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1173 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1174 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1223 = match if_126_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1224 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1174, v1223]) { Ok(v) => v, Err(e) => return Err(e) };
let v1225 = match eo__24str_5fflatten(s, v1224) { Ok(v) => v, Err(e) => return Err(e) };
let v1226 = match s.builtin_list(EvalOp::ListRev, &[v1173, v1225]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1226)
}
Some(false) => {
let v1227 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1276 = match if_132_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1277 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1227, v1276]) { Ok(v) => v, Err(e) => return Err(e) };
let v1278 = match eo__24str_5fflatten(s, v1277) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1278)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_134_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1283 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1284 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1285 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1284, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1286 = match s.builtin_list(EvalOp::ListRev, &[v1283, v1285]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1286)
}
Some(false) => {
let v1287 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1288 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1287, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1288)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_135_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1297 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1298 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1299 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1298, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1300 = match s.builtin_list(EvalOp::ListRev, &[v1297, v1299]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1300)
}
Some(false) => {
let v1301 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1302 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1301, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1302)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_136_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1280 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1281 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1282 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1289 = match if_134_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1290 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1291 = match s.builtin_list(EvalOp::ListNth, &[v1282, v1289, v1290]) { Ok(v) => v, Err(e) => return Err(e) };
let v1292 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1281, v1291]) { Ok(v) => v, Err(e) => return Err(e) };
let v1293 = match eo__24str_5fflatten(s, v1292) { Ok(v) => v, Err(e) => return Err(e) };
let v1294 = match s.builtin_list(EvalOp::ListRev, &[v1280, v1293]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1294)
}
Some(false) => {
let v1295 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1296 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1303 = match if_135_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1304 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1305 = match s.builtin_list(EvalOp::ListNth, &[v1296, v1303, v1304]) { Ok(v) => v, Err(e) => return Err(e) };
let v1306 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1295, v1305]) { Ok(v) => v, Err(e) => return Err(e) };
let v1307 = match eo__24str_5fflatten(s, v1306) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1307)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_137_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1321 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1322 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1323 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1322, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1324 = match s.builtin_list(EvalOp::ListRev, &[v1321, v1323]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1324)
}
Some(false) => {
let v1325 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1326 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1325, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1326)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_138_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1337 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1338 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1339 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1338, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1340 = match s.builtin_list(EvalOp::ListRev, &[v1337, v1339]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1340)
}
Some(false) => {
let v1341 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1342 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1341, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1342)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_139_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1348 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1349 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1350 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1349, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1351 = match s.builtin_list(EvalOp::ListRev, &[v1348, v1350]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1351)
}
Some(false) => {
let v1352 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1353 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1352, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1353)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_140_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1362 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1363 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1364 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1363, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1365 = match s.builtin_list(EvalOp::ListRev, &[v1362, v1364]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1365)
}
Some(false) => {
let v1366 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1367 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1366, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1367)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_141_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1373 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1374 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1375 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1374, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1376 = match s.builtin_list(EvalOp::ListRev, &[v1373, v1375]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1376)
}
Some(false) => {
let v1377 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1378 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1377, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1378)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_142_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1345: Term, v1346: Term, v1359: Term) -> CheckResult<Term> {
let v1360 = match s.builtin_core(EvalOp::Extract, &[v1345, v1346, v1359]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1360)
}
pub(super) fn if_143_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1336 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1343 = match if_138_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1344 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1345 = match s.builtin_list(EvalOp::ListNth, &[v1336, v1343, v1344]) { Ok(v) => v, Err(e) => return Err(e) };
let v1346 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1347 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1354 = match if_139_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1355 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1356 = match s.builtin_list(EvalOp::ListNth, &[v1347, v1354, v1355]) { Ok(v) => v, Err(e) => return Err(e) };
let v1357 = match s.builtin_core(EvalOp::Length, &[v1356]) { Ok(v) => v, Err(e) => return Err(e) };
let v1358 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1359 = match s.builtin_core(EvalOp::Add, &[v1357, v1358]) { Ok(v) => v, Err(e) => return Err(e) };
more_142_eo__24eo_5fprog_5fconcat_5fcprop(s, v1345, v1346, v1359)
}
Some(false) => {
let v1361 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1368 = match if_140_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1369 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1370 = match s.builtin_list(EvalOp::ListNth, &[v1361, v1368, v1369]) { Ok(v) => v, Err(e) => return Err(e) };
let v1371 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1372 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1379 = match if_141_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1380 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1381 = match s.builtin_list(EvalOp::ListNth, &[v1372, v1379, v1380]) { Ok(v) => v, Err(e) => return Err(e) };
let v1382 = match s.builtin_core(EvalOp::Length, &[v1381]) { Ok(v) => v, Err(e) => return Err(e) };
let v1383 = match s.builtin_core(EvalOp::Extract, &[v1370, v1371, v1382]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1383)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_144_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1390 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1391 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1392 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1391, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1393 = match s.builtin_list(EvalOp::ListRev, &[v1390, v1392]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1393)
}
Some(false) => {
let v1394 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1395 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1394, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1395)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_145_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1401 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1402 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1403 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1402, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1404 = match s.builtin_list(EvalOp::ListRev, &[v1401, v1403]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1404)
}
Some(false) => {
let v1405 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1406 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1405, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1406)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_146_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1415 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1416 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1417 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1416, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1418 = match s.builtin_list(EvalOp::ListRev, &[v1415, v1417]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1418)
}
Some(false) => {
let v1419 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1420 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1419, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1420)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_147_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1426 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1427 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1428 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1427, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1429 = match s.builtin_list(EvalOp::ListRev, &[v1426, v1428]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1429)
}
Some(false) => {
let v1430 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1431 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1430, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1431)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_148_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1398: Term, v1399: Term, v1412: Term) -> CheckResult<Term> {
let v1413 = match s.builtin_core(EvalOp::Extract, &[v1398, v1399, v1412]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1413)
}
pub(super) fn if_149_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1389 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1396 = match if_144_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1397 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1398 = match s.builtin_list(EvalOp::ListNth, &[v1389, v1396, v1397]) { Ok(v) => v, Err(e) => return Err(e) };
let v1399 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1400 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1407 = match if_145_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1408 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1409 = match s.builtin_list(EvalOp::ListNth, &[v1400, v1407, v1408]) { Ok(v) => v, Err(e) => return Err(e) };
let v1410 = match s.builtin_core(EvalOp::Length, &[v1409]) { Ok(v) => v, Err(e) => return Err(e) };
let v1411 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1412 = match s.builtin_core(EvalOp::Add, &[v1410, v1411]) { Ok(v) => v, Err(e) => return Err(e) };
more_148_eo__24eo_5fprog_5fconcat_5fcprop(s, v1398, v1399, v1412)
}
Some(false) => {
let v1414 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1421 = match if_146_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1422 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1423 = match s.builtin_list(EvalOp::ListNth, &[v1414, v1421, v1422]) { Ok(v) => v, Err(e) => return Err(e) };
let v1424 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1425 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1432 = match if_147_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1433 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1434 = match s.builtin_list(EvalOp::ListNth, &[v1425, v1432, v1433]) { Ok(v) => v, Err(e) => return Err(e) };
let v1435 = match s.builtin_core(EvalOp::Length, &[v1434]) { Ok(v) => v, Err(e) => return Err(e) };
let v1436 = match s.builtin_core(EvalOp::Extract, &[v1423, v1424, v1435]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1436)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_150_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1334 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1335 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1384 = match if_143_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1385 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1335, v1384]) { Ok(v) => v, Err(e) => return Err(e) };
let v1386 = match eo__24str_5fflatten(s, v1385) { Ok(v) => v, Err(e) => return Err(e) };
let v1387 = match s.builtin_list(EvalOp::ListRev, &[v1334, v1386]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1387)
}
Some(false) => {
let v1388 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1437 = match if_149_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1438 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1388, v1437]) { Ok(v) => v, Err(e) => return Err(e) };
let v1439 = match eo__24str_5fflatten(s, v1438) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1439)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_151_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1444 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1445 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1446 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1445, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1447 = match s.builtin_list(EvalOp::ListRev, &[v1444, v1446]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1447)
}
Some(false) => {
let v1448 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1449 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1448, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1449)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_152_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1458 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1459 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1460 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1459, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1461 = match s.builtin_list(EvalOp::ListRev, &[v1458, v1460]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1461)
}
Some(false) => {
let v1462 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1463 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1462, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1463)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_153_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1441 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1442 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1443 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1450 = match if_151_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1451 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1452 = match s.builtin_list(EvalOp::ListNth, &[v1443, v1450, v1451]) { Ok(v) => v, Err(e) => return Err(e) };
let v1453 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1442, v1452]) { Ok(v) => v, Err(e) => return Err(e) };
let v1454 = match eo__24str_5fflatten(s, v1453) { Ok(v) => v, Err(e) => return Err(e) };
let v1455 = match s.builtin_list(EvalOp::ListRev, &[v1441, v1454]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1455)
}
Some(false) => {
let v1456 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1457 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1464 = match if_152_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1465 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1466 = match s.builtin_list(EvalOp::ListNth, &[v1457, v1464, v1465]) { Ok(v) => v, Err(e) => return Err(e) };
let v1467 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1456, v1466]) { Ok(v) => v, Err(e) => return Err(e) };
let v1468 = match eo__24str_5fflatten(s, v1467) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1468)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_154_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1481 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1482 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1483 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1482, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1484 = match s.builtin_list(EvalOp::ListRev, &[v1481, v1483]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1484)
}
Some(false) => {
let v1485 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1486 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1485, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1486)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_155_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1497 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1498 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1499 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1498, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1500 = match s.builtin_list(EvalOp::ListRev, &[v1497, v1499]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1500)
}
Some(false) => {
let v1501 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1502 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1501, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1502)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_156_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1508 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1509 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1510 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1509, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1511 = match s.builtin_list(EvalOp::ListRev, &[v1508, v1510]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1511)
}
Some(false) => {
let v1512 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1513 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1512, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1513)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_157_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1522 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1523 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1524 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1523, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1525 = match s.builtin_list(EvalOp::ListRev, &[v1522, v1524]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1525)
}
Some(false) => {
let v1526 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1527 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1526, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1527)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_158_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1533 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1534 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1535 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1534, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1536 = match s.builtin_list(EvalOp::ListRev, &[v1533, v1535]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1536)
}
Some(false) => {
let v1537 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1538 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1537, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1538)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_159_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1505: Term, v1506: Term, v1519: Term) -> CheckResult<Term> {
let v1520 = match s.builtin_core(EvalOp::Extract, &[v1505, v1506, v1519]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1520)
}
pub(super) fn if_160_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1496 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1503 = match if_155_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1504 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1505 = match s.builtin_list(EvalOp::ListNth, &[v1496, v1503, v1504]) { Ok(v) => v, Err(e) => return Err(e) };
let v1506 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1507 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1514 = match if_156_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1515 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1516 = match s.builtin_list(EvalOp::ListNth, &[v1507, v1514, v1515]) { Ok(v) => v, Err(e) => return Err(e) };
let v1517 = match s.builtin_core(EvalOp::Length, &[v1516]) { Ok(v) => v, Err(e) => return Err(e) };
let v1518 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1519 = match s.builtin_core(EvalOp::Add, &[v1517, v1518]) { Ok(v) => v, Err(e) => return Err(e) };
more_159_eo__24eo_5fprog_5fconcat_5fcprop(s, v1505, v1506, v1519)
}
Some(false) => {
let v1521 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1528 = match if_157_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1529 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1530 = match s.builtin_list(EvalOp::ListNth, &[v1521, v1528, v1529]) { Ok(v) => v, Err(e) => return Err(e) };
let v1531 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1532 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1539 = match if_158_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1540 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1541 = match s.builtin_list(EvalOp::ListNth, &[v1532, v1539, v1540]) { Ok(v) => v, Err(e) => return Err(e) };
let v1542 = match s.builtin_core(EvalOp::Length, &[v1541]) { Ok(v) => v, Err(e) => return Err(e) };
let v1543 = match s.builtin_core(EvalOp::Extract, &[v1530, v1531, v1542]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1543)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_161_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1550 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1551 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1552 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1551, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1553 = match s.builtin_list(EvalOp::ListRev, &[v1550, v1552]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1553)
}
Some(false) => {
let v1554 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1555 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1554, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1555)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_162_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1561 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1562 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1563 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1562, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1564 = match s.builtin_list(EvalOp::ListRev, &[v1561, v1563]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1564)
}
Some(false) => {
let v1565 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1566 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1565, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1566)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_163_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1575 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1576 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1577 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1576, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1578 = match s.builtin_list(EvalOp::ListRev, &[v1575, v1577]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1578)
}
Some(false) => {
let v1579 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1580 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1579, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1580)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_164_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1586 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1587 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1588 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1587, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1589 = match s.builtin_list(EvalOp::ListRev, &[v1586, v1588]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1589)
}
Some(false) => {
let v1590 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1591 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1590, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1591)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_165_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1558: Term, v1559: Term, v1572: Term) -> CheckResult<Term> {
let v1573 = match s.builtin_core(EvalOp::Extract, &[v1558, v1559, v1572]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1573)
}
pub(super) fn if_166_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1549 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1556 = match if_161_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1557 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1558 = match s.builtin_list(EvalOp::ListNth, &[v1549, v1556, v1557]) { Ok(v) => v, Err(e) => return Err(e) };
let v1559 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1560 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1567 = match if_162_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1568 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1569 = match s.builtin_list(EvalOp::ListNth, &[v1560, v1567, v1568]) { Ok(v) => v, Err(e) => return Err(e) };
let v1570 = match s.builtin_core(EvalOp::Length, &[v1569]) { Ok(v) => v, Err(e) => return Err(e) };
let v1571 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v1572 = match s.builtin_core(EvalOp::Add, &[v1570, v1571]) { Ok(v) => v, Err(e) => return Err(e) };
more_165_eo__24eo_5fprog_5fconcat_5fcprop(s, v1558, v1559, v1572)
}
Some(false) => {
let v1574 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1581 = match if_163_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1582 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1583 = match s.builtin_list(EvalOp::ListNth, &[v1574, v1581, v1582]) { Ok(v) => v, Err(e) => return Err(e) };
let v1584 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1585 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1592 = match if_164_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1593 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1594 = match s.builtin_list(EvalOp::ListNth, &[v1585, v1592, v1593]) { Ok(v) => v, Err(e) => return Err(e) };
let v1595 = match s.builtin_core(EvalOp::Length, &[v1594]) { Ok(v) => v, Err(e) => return Err(e) };
let v1596 = match s.builtin_core(EvalOp::Extract, &[v1583, v1584, v1595]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1596)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_167_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1494 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1495 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1544 = match if_160_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1545 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1495, v1544]) { Ok(v) => v, Err(e) => return Err(e) };
let v1546 = match eo__24str_5fflatten(s, v1545) { Ok(v) => v, Err(e) => return Err(e) };
let v1547 = match s.builtin_list(EvalOp::ListRev, &[v1494, v1546]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1547)
}
Some(false) => {
let v1548 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1597 = match if_166_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1598 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1548, v1597]) { Ok(v) => v, Err(e) => return Err(e) };
let v1599 = match eo__24str_5fflatten(s, v1598) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1599)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_168_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1604 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1605 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1606 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1605, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1607 = match s.builtin_list(EvalOp::ListRev, &[v1604, v1606]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1607)
}
Some(false) => {
let v1608 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1609 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1608, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1609)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_169_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1618 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1619 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1620 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1619, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1621 = match s.builtin_list(EvalOp::ListRev, &[v1618, v1620]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1621)
}
Some(false) => {
let v1622 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1623 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1622, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1623)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_170_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1601 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1602 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1603 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1610 = match if_168_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1611 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1612 = match s.builtin_list(EvalOp::ListNth, &[v1603, v1610, v1611]) { Ok(v) => v, Err(e) => return Err(e) };
let v1613 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1602, v1612]) { Ok(v) => v, Err(e) => return Err(e) };
let v1614 = match eo__24str_5fflatten(s, v1613) { Ok(v) => v, Err(e) => return Err(e) };
let v1615 = match s.builtin_list(EvalOp::ListRev, &[v1601, v1614]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1615)
}
Some(false) => {
let v1616 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1617 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1624 = match if_169_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1625 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1626 = match s.builtin_list(EvalOp::ListNth, &[v1617, v1624, v1625]) { Ok(v) => v, Err(e) => return Err(e) };
let v1627 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1616, v1626]) { Ok(v) => v, Err(e) => return Err(e) };
let v1628 = match eo__24str_5fflatten(s, v1627) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1628)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
pub(super) fn if_0_eo__24str_5fis_5fcompatible(s: &mut Store, condition: Term, v5: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24are_5fdistinct_5fterms_5ftype(s, v5, v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24str_5fis_5fcompatible(s: &mut Store, v18: Term, v19: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_1_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
let v18 = match if_0_eo__24str_5fis_5fcompatible(s, v14, v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_1_eo__24str_5fis_5fcompatible(s, v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v21)))
}
pub(super) fn case_2_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24str_5fis_5fempty(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::Or, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn step_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fis_5fcompatible(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fis_5fcompatible(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fis_5fcompatible(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5fis_5fcompatible(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fis_5fcompatible(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$str_is_compatible"
pub fn eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1063), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fis_5fcompatible(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1063), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$str_overlap_rec"
pub fn eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1078), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5foverlap_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1078), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5foverlap_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5foverlap_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24str_5fis_5fcompatible(s, v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24str_5foverlap_5frec(s, v10, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn if_0_eo__24str_5foverlap_5frec(s: &mut Store, condition: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24str_5foverlap_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_176_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, v7: Term, v1600: Term, v1493: Term, v1492: Term, v1478: Term, v1477: Term, v1152: Term) -> CheckResult<Term> {
let v1629 = match if_170_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1630 = match eo__24str_5foverlap_5frec(s, v1600, v1629) { Ok(v) => v, Err(e) => return Err(e) };
let v1631 = match s.builtin_core(EvalOp::Add, &[v1493, v1630]) { Ok(v) => v, Err(e) => return Err(e) };
let v1632 = match s.apply(v1492, v1631) { Ok(v) => v, Err(e) => return Err(e) };
let v1633 = match eo__24eo_5ftypeof(s, v1632) { Ok(v) => v, Err(e) => return Err(e) };
let v1634 = match eo__24eo_5fnil(s, v1478, v1633) { Ok(v) => v, Err(e) => return Err(e) };
let v1635 = match s.apply(v1477, v1634) { Ok(v) => v, Err(e) => return Err(e) };
let v1636 = match s.apply(v1152, v1635) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1636)
}
pub(super) fn more_175_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1153: Term, v1476: Term, a0: Term, v4: Term, v7: Term, v1152: Term) -> CheckResult<Term> {
let v1477 = match s.apply(v1153, v1476) { Ok(v) => v, Err(e) => return Err(e) };
let v1478 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1479 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1480 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1487 = match if_154_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1488 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1489 = match s.builtin_list(EvalOp::ListNth, &[v1480, v1487, v1488]) { Ok(v) => v, Err(e) => return Err(e) };
let v1490 = match s.apply(v1479, v1489) { Ok(v) => v, Err(e) => return Err(e) };
let v1491 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1492 = match s.apply(v1490, v1491) { Ok(v) => v, Err(e) => return Err(e) };
let v1493 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1600 = match if_167_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_176_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7, v1600, v1493, v1492, v1478, v1477, v1152)
}
pub(super) fn more_174_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1330: Term, a0: Term, v4: Term, v7: Term, v1318: Term, v1317: Term, v1313: Term, v1154: Term, v1153: Term, v1152: Term) -> CheckResult<Term> {
let v1331 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1332 = match s.apply(v1330, v1331) { Ok(v) => v, Err(e) => return Err(e) };
let v1333 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1440 = match if_150_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1469 = match if_153_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1470 = match eo__24str_5foverlap_5frec(s, v1440, v1469) { Ok(v) => v, Err(e) => return Err(e) };
let v1471 = match s.builtin_core(EvalOp::Add, &[v1333, v1470]) { Ok(v) => v, Err(e) => return Err(e) };
let v1472 = match s.apply(v1332, v1471) { Ok(v) => v, Err(e) => return Err(e) };
let v1473 = match s.apply(v1318, v1472) { Ok(v) => v, Err(e) => return Err(e) };
let v1474 = match s.apply(v1317, v1473) { Ok(v) => v, Err(e) => return Err(e) };
let v1475 = match s.apply(v1313, v1474) { Ok(v) => v, Err(e) => return Err(e) };
let v1476 = match s.apply(v1154, v1475) { Ok(v) => v, Err(e) => return Err(e) };
more_175_eo__24eo_5fprog_5fconcat_5fcprop(s, v1153, v1476, a0, v4, v7, v1152)
}
pub(super) fn more_173_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1156: Term, v1312: Term, v24: Term, a0: Term, v4: Term, v7: Term, v1154: Term, v1153: Term, v1152: Term) -> CheckResult<Term> {
let v1313 = match s.apply(v1156, v1312) { Ok(v) => v, Err(e) => return Err(e) };
let v1314 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1315 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1316 = match s.apply(v1315, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v1317 = match s.apply(v1314, v1316) { Ok(v) => v, Err(e) => return Err(e) };
let v1318 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1319 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1320 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1327 = match if_137_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1328 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1329 = match s.builtin_list(EvalOp::ListNth, &[v1320, v1327, v1328]) { Ok(v) => v, Err(e) => return Err(e) };
let v1330 = match s.apply(v1319, v1329) { Ok(v) => v, Err(e) => return Err(e) };
more_174_eo__24eo_5fprog_5fconcat_5fcprop(s, v1330, a0, v4, v7, v1318, v1317, v1313, v1154, v1153, v1152)
}
pub(super) fn more_172_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1159: Term, v1166: Term, v1158: Term, a0: Term, v4: Term, v7: Term, v1157: Term, v1156: Term, v24: Term, v1154: Term, v1153: Term, v1152: Term) -> CheckResult<Term> {
let v1167 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1168 = match s.builtin_list(EvalOp::ListNth, &[v1159, v1166, v1167]) { Ok(v) => v, Err(e) => return Err(e) };
let v1169 = match s.apply(v1158, v1168) { Ok(v) => v, Err(e) => return Err(e) };
let v1170 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1171 = match s.apply(v1169, v1170) { Ok(v) => v, Err(e) => return Err(e) };
let v1172 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1279 = match if_133_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1308 = match if_136_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1309 = match eo__24str_5foverlap_5frec(s, v1279, v1308) { Ok(v) => v, Err(e) => return Err(e) };
let v1310 = match s.builtin_core(EvalOp::Add, &[v1172, v1309]) { Ok(v) => v, Err(e) => return Err(e) };
let v1311 = match s.apply(v1171, v1310) { Ok(v) => v, Err(e) => return Err(e) };
let v1312 = match s.apply(v1157, v1311) { Ok(v) => v, Err(e) => return Err(e) };
more_173_eo__24eo_5fprog_5fconcat_5fcprop(s, v1156, v1312, v24, a0, v4, v7, v1154, v1153, v1152)
}
pub(super) fn more_171_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1119: Term, v1148: Term, v1012: Term, v1011: Term, v997: Term, v24: Term, a0: Term, v4: Term, v7: Term) -> CheckResult<Term> {
let v1149 = match eo__24str_5foverlap_5frec(s, v1119, v1148) { Ok(v) => v, Err(e) => return Err(e) };
let v1150 = match s.builtin_core(EvalOp::Add, &[v1012, v1149]) { Ok(v) => v, Err(e) => return Err(e) };
let v1151 = match s.apply(v1011, v1150) { Ok(v) => v, Err(e) => return Err(e) };
let v1152 = match s.apply(v997, v1151) { Ok(v) => v, Err(e) => return Err(e) };
let v1153 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1154 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1155 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1156 = match s.apply(v1155, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v1157 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1158 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1159 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1166 = match if_120_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_172_eo__24eo_5fprog_5fconcat_5fcprop(s, v1159, v1166, v1158, a0, v4, v7, v1157, v1156, v24, v1154, v1153, v1152)
}
pub(super) fn if_1_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v52 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v53, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_list(EvalOp::ListRev, &[v52, v54]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v55)
}
Some(false) => {
let v56 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v56, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v65 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v66, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_list(EvalOp::ListRev, &[v65, v67]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v68)
}
Some(false) => {
let v69 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v69, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v80 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v81, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListRev, &[v80, v82]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v83)
}
Some(false) => {
let v84 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v84, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v85)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
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
pub(super) fn if_5_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v105 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v106, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_list(EvalOp::ListRev, &[v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v108)
}
Some(false) => {
let v109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v109, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v110)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
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
pub(super) fn more_7_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v88: Term, v89: Term, v102: Term) -> CheckResult<Term> {
let v103 = match s.builtin_core(EvalOp::Extract, &[v88, v89, v102]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v103)
}
pub(super) fn if_8_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v79 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match if_3_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.builtin_list(EvalOp::ListNth, &[v79, v86, v87]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match if_4_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.builtin_list(EvalOp::ListNth, &[v90, v97, v98]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.builtin_core(EvalOp::Length, &[v99]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_core(EvalOp::Add, &[v100, v101]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fconcat_5fcprop(s, v88, v89, v102)
}
Some(false) => {
let v104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match if_5_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.builtin_list(EvalOp::ListNth, &[v104, v111, v112]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match if_6_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_list(EvalOp::ListNth, &[v115, v122, v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.builtin_core(EvalOp::Length, &[v124]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.builtin_core(EvalOp::Extract, &[v113, v114, v125]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v126)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v133 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v134, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.builtin_list(EvalOp::ListRev, &[v133, v135]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v136)
}
Some(false) => {
let v137 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v137, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v138)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v144 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v145, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_list(EvalOp::ListRev, &[v144, v146]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v147)
}
Some(false) => {
let v148 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v148, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v149)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v158 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v159, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_list(EvalOp::ListRev, &[v158, v160]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v161)
}
Some(false) => {
let v162 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v162, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v163)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_12_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v169 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v170, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.builtin_list(EvalOp::ListRev, &[v169, v171]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v172)
}
Some(false) => {
let v173 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v173, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v174)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_13_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v141: Term, v142: Term, v155: Term) -> CheckResult<Term> {
let v156 = match s.builtin_core(EvalOp::Extract, &[v141, v142, v155]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v156)
}
pub(super) fn if_14_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v132 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match if_9_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_list(EvalOp::ListNth, &[v132, v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match if_10_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.builtin_list(EvalOp::ListNth, &[v143, v150, v151]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.builtin_core(EvalOp::Length, &[v152]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.builtin_core(EvalOp::Add, &[v153, v154]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fconcat_5fcprop(s, v141, v142, v155)
}
Some(false) => {
let v157 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match if_11_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.builtin_list(EvalOp::ListNth, &[v157, v164, v165]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match if_12_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListNth, &[v168, v175, v176]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.builtin_core(EvalOp::Length, &[v177]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_core(EvalOp::Extract, &[v166, v167, v178]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v179)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match if_8_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v78, v127]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24str_5fflatten(s, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_list(EvalOp::ListRev, &[v77, v129]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v130)
}
Some(false) => {
let v131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match if_14_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v131, v180]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match eo__24str_5fflatten(s, v181) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v182)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v187 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v188, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.builtin_list(EvalOp::ListRev, &[v187, v189]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v190)
}
Some(false) => {
let v191 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v191, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v192)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v201 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v202, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.builtin_list(EvalOp::ListRev, &[v201, v203]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v204)
}
Some(false) => {
let v205 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v205, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v206)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v184 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match if_16_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.builtin_list(EvalOp::ListNth, &[v186, v193, v194]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v185, v195]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match eo__24str_5fflatten(s, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.builtin_list(EvalOp::ListRev, &[v184, v197]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v198)
}
Some(false) => {
let v199 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match if_17_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.builtin_list(EvalOp::ListNth, &[v200, v207, v208]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v199, v209]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match eo__24str_5fflatten(s, v210) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v211)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v221 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v222, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.builtin_list(EvalOp::ListRev, &[v221, v223]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v224)
}
Some(false) => {
let v225 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v225, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v226)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_20_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v232 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v233, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.builtin_list(EvalOp::ListRev, &[v232, v234]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v235)
}
Some(false) => {
let v236 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v236, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v237)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v246 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v247, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.builtin_list(EvalOp::ListRev, &[v246, v248]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v249)
}
Some(false) => {
let v250 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v250, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v251)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_22_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v257 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v258, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.builtin_list(EvalOp::ListRev, &[v257, v259]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v260)
}
Some(false) => {
let v261 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v261, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v262)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_23_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v229: Term, v230: Term, v243: Term) -> CheckResult<Term> {
let v244 = match s.builtin_core(EvalOp::Extract, &[v229, v230, v243]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v244)
}
pub(super) fn if_24_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v220 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match if_19_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.builtin_list(EvalOp::ListNth, &[v220, v227, v228]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match if_20_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.builtin_list(EvalOp::ListNth, &[v231, v238, v239]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.builtin_core(EvalOp::Length, &[v240]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.builtin_core(EvalOp::Add, &[v241, v242]) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24eo_5fprog_5fconcat_5fcprop(s, v229, v230, v243)
}
Some(false) => {
let v245 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match if_21_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.builtin_list(EvalOp::ListNth, &[v245, v252, v253]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match if_22_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.builtin_list(EvalOp::ListNth, &[v256, v263, v264]) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.builtin_core(EvalOp::Length, &[v265]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.builtin_core(EvalOp::Extract, &[v254, v255, v266]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v267)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_25_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v274 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v275, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.builtin_list(EvalOp::ListRev, &[v274, v276]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v277)
}
Some(false) => {
let v278 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v278, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v279)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_26_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v285 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v286, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.builtin_list(EvalOp::ListRev, &[v285, v287]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v288)
}
Some(false) => {
let v289 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v289, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v290)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_27_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v299 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v300, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.builtin_list(EvalOp::ListRev, &[v299, v301]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v302)
}
Some(false) => {
let v303 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v303, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v304)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_28_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v310 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v311, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.builtin_list(EvalOp::ListRev, &[v310, v312]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v313)
}
Some(false) => {
let v314 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v314, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v315)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_29_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v282: Term, v283: Term, v296: Term) -> CheckResult<Term> {
let v297 = match s.builtin_core(EvalOp::Extract, &[v282, v283, v296]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v297)
}
pub(super) fn if_30_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v273 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match if_25_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.builtin_list(EvalOp::ListNth, &[v273, v280, v281]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match if_26_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.builtin_list(EvalOp::ListNth, &[v284, v291, v292]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.builtin_core(EvalOp::Length, &[v293]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.builtin_core(EvalOp::Add, &[v294, v295]) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24eo_5fprog_5fconcat_5fcprop(s, v282, v283, v296)
}
Some(false) => {
let v298 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match if_27_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.builtin_list(EvalOp::ListNth, &[v298, v305, v306]) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match if_28_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.builtin_list(EvalOp::ListNth, &[v309, v316, v317]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.builtin_core(EvalOp::Length, &[v318]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.builtin_core(EvalOp::Extract, &[v307, v308, v319]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v320)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_31_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v218 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match if_24_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v219, v268]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match eo__24str_5fflatten(s, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.builtin_list(EvalOp::ListRev, &[v218, v270]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v271)
}
Some(false) => {
let v272 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match if_30_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v272, v321]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match eo__24str_5fflatten(s, v322) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v323)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_32_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v328 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v329, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.builtin_list(EvalOp::ListRev, &[v328, v330]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v331)
}
Some(false) => {
let v332 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v332, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v333)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_33_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v342 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v343, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.builtin_list(EvalOp::ListRev, &[v342, v344]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v345)
}
Some(false) => {
let v346 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v346, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v347)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_34_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v325 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match if_32_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.builtin_list(EvalOp::ListNth, &[v327, v334, v335]) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v326, v336]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match eo__24str_5fflatten(s, v337) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.builtin_list(EvalOp::ListRev, &[v325, v338]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v339)
}
Some(false) => {
let v340 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match if_33_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.builtin_list(EvalOp::ListNth, &[v341, v348, v349]) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v340, v350]) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match eo__24str_5fflatten(s, v351) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v352)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_35_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v365 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v366, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.builtin_list(EvalOp::ListRev, &[v365, v367]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v368)
}
Some(false) => {
let v369 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v369, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v370)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_36_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v378 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v379, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.builtin_list(EvalOp::ListRev, &[v378, v380]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v381)
}
Some(false) => {
let v382 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v382, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v383)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_37_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v393 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v394, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.builtin_list(EvalOp::ListRev, &[v393, v395]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v396)
}
Some(false) => {
let v397 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v397, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v398)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_38_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v404 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v405, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.builtin_list(EvalOp::ListRev, &[v404, v406]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v407)
}
Some(false) => {
let v408 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v408, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v409)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_39_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
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
pub(super) fn if_40_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v429 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v430, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match s.builtin_list(EvalOp::ListRev, &[v429, v431]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v432)
}
Some(false) => {
let v433 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v433, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v434)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_41_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v401: Term, v402: Term, v415: Term) -> CheckResult<Term> {
let v416 = match s.builtin_core(EvalOp::Extract, &[v401, v402, v415]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v416)
}
pub(super) fn if_42_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v392 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match if_37_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.builtin_list(EvalOp::ListNth, &[v392, v399, v400]) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match if_38_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.builtin_list(EvalOp::ListNth, &[v403, v410, v411]) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.builtin_core(EvalOp::Length, &[v412]) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.builtin_core(EvalOp::Add, &[v413, v414]) { Ok(v) => v, Err(e) => return Err(e) };
more_41_eo__24eo_5fprog_5fconcat_5fcprop(s, v401, v402, v415)
}
Some(false) => {
let v417 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match if_39_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.builtin_list(EvalOp::ListNth, &[v417, v424, v425]) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match if_40_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match s.builtin_list(EvalOp::ListNth, &[v428, v435, v436]) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.builtin_core(EvalOp::Length, &[v437]) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match s.builtin_core(EvalOp::Extract, &[v426, v427, v438]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v439)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_43_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v446 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v448 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v447, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match s.builtin_list(EvalOp::ListRev, &[v446, v448]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v449)
}
Some(false) => {
let v450 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v450, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v451)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_44_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v457 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v458, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.builtin_list(EvalOp::ListRev, &[v457, v459]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v460)
}
Some(false) => {
let v461 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v461, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v462)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_45_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v471 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v473 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v472, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v474 = match s.builtin_list(EvalOp::ListRev, &[v471, v473]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v474)
}
Some(false) => {
let v475 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v476 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v475, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v476)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_46_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v482 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v483 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v484 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v483, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v485 = match s.builtin_list(EvalOp::ListRev, &[v482, v484]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v485)
}
Some(false) => {
let v486 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v487 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v486, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v487)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_47_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v454: Term, v455: Term, v468: Term) -> CheckResult<Term> {
let v469 = match s.builtin_core(EvalOp::Extract, &[v454, v455, v468]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v469)
}
pub(super) fn if_48_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v445 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match if_43_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match s.builtin_list(EvalOp::ListNth, &[v445, v452, v453]) { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v463 = match if_44_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match s.builtin_list(EvalOp::ListNth, &[v456, v463, v464]) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.builtin_core(EvalOp::Length, &[v465]) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match s.builtin_core(EvalOp::Add, &[v466, v467]) { Ok(v) => v, Err(e) => return Err(e) };
more_47_eo__24eo_5fprog_5fconcat_5fcprop(s, v454, v455, v468)
}
Some(false) => {
let v470 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v477 = match if_45_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v478 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v479 = match s.builtin_list(EvalOp::ListNth, &[v470, v477, v478]) { Ok(v) => v, Err(e) => return Err(e) };
let v480 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v481 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v488 = match if_46_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v489 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v490 = match s.builtin_list(EvalOp::ListNth, &[v481, v488, v489]) { Ok(v) => v, Err(e) => return Err(e) };
let v491 = match s.builtin_core(EvalOp::Length, &[v490]) { Ok(v) => v, Err(e) => return Err(e) };
let v492 = match s.builtin_core(EvalOp::Extract, &[v479, v480, v491]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v492)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_49_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v390 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match if_42_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v391, v440]) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match eo__24str_5fflatten(s, v441) { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.builtin_list(EvalOp::ListRev, &[v390, v442]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v443)
}
Some(false) => {
let v444 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v493 = match if_48_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v494 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v444, v493]) { Ok(v) => v, Err(e) => return Err(e) };
let v495 = match eo__24str_5fflatten(s, v494) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v495)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_50_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v500 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v501 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v502 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v501, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v503 = match s.builtin_list(EvalOp::ListRev, &[v500, v502]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v503)
}
Some(false) => {
let v504 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v505 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v504, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v505)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_51_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v514 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v515 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v516 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v515, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v517 = match s.builtin_list(EvalOp::ListRev, &[v514, v516]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v517)
}
Some(false) => {
let v518 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v519 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v518, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v519)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_52_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v497 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v498 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v499 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v506 = match if_50_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v507 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v508 = match s.builtin_list(EvalOp::ListNth, &[v499, v506, v507]) { Ok(v) => v, Err(e) => return Err(e) };
let v509 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v498, v508]) { Ok(v) => v, Err(e) => return Err(e) };
let v510 = match eo__24str_5fflatten(s, v509) { Ok(v) => v, Err(e) => return Err(e) };
let v511 = match s.builtin_list(EvalOp::ListRev, &[v497, v510]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v511)
}
Some(false) => {
let v512 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v513 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v520 = match if_51_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v521 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v522 = match s.builtin_list(EvalOp::ListNth, &[v513, v520, v521]) { Ok(v) => v, Err(e) => return Err(e) };
let v523 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v512, v522]) { Ok(v) => v, Err(e) => return Err(e) };
let v524 = match eo__24str_5fflatten(s, v523) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v524)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_53_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v534 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v535 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v536 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v535, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v537 = match s.builtin_list(EvalOp::ListRev, &[v534, v536]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v537)
}
Some(false) => {
let v538 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v539 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v538, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v539)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_54_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v545 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v546 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v547 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v546, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v548 = match s.builtin_list(EvalOp::ListRev, &[v545, v547]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v548)
}
Some(false) => {
let v549 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v550 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v549, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v550)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_55_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v559 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v560 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v561 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v560, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v562 = match s.builtin_list(EvalOp::ListRev, &[v559, v561]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v562)
}
Some(false) => {
let v563 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v564 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v563, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v564)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_56_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v570 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v571 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v572 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v571, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v573 = match s.builtin_list(EvalOp::ListRev, &[v570, v572]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v573)
}
Some(false) => {
let v574 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v575 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v574, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v575)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_57_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v542: Term, v543: Term, v556: Term) -> CheckResult<Term> {
let v557 = match s.builtin_core(EvalOp::Extract, &[v542, v543, v556]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v557)
}
pub(super) fn if_58_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v533 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v540 = match if_53_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v541 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v542 = match s.builtin_list(EvalOp::ListNth, &[v533, v540, v541]) { Ok(v) => v, Err(e) => return Err(e) };
let v543 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v544 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v551 = match if_54_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v552 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v553 = match s.builtin_list(EvalOp::ListNth, &[v544, v551, v552]) { Ok(v) => v, Err(e) => return Err(e) };
let v554 = match s.builtin_core(EvalOp::Length, &[v553]) { Ok(v) => v, Err(e) => return Err(e) };
let v555 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v556 = match s.builtin_core(EvalOp::Add, &[v554, v555]) { Ok(v) => v, Err(e) => return Err(e) };
more_57_eo__24eo_5fprog_5fconcat_5fcprop(s, v542, v543, v556)
}
Some(false) => {
let v558 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v565 = match if_55_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v566 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v567 = match s.builtin_list(EvalOp::ListNth, &[v558, v565, v566]) { Ok(v) => v, Err(e) => return Err(e) };
let v568 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v569 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v576 = match if_56_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v577 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v578 = match s.builtin_list(EvalOp::ListNth, &[v569, v576, v577]) { Ok(v) => v, Err(e) => return Err(e) };
let v579 = match s.builtin_core(EvalOp::Length, &[v578]) { Ok(v) => v, Err(e) => return Err(e) };
let v580 = match s.builtin_core(EvalOp::Extract, &[v567, v568, v579]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v580)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_59_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v587 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v588 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v589 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v588, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v590 = match s.builtin_list(EvalOp::ListRev, &[v587, v589]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v590)
}
Some(false) => {
let v591 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v592 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v591, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v592)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_60_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v598 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v599 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v600 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v599, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v601 = match s.builtin_list(EvalOp::ListRev, &[v598, v600]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v601)
}
Some(false) => {
let v602 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v603 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v602, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v603)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_61_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v612 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v613 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v614 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v613, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v615 = match s.builtin_list(EvalOp::ListRev, &[v612, v614]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v615)
}
Some(false) => {
let v616 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v617 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v616, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v617)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_62_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v623 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v624 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v625 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v624, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v626 = match s.builtin_list(EvalOp::ListRev, &[v623, v625]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v626)
}
Some(false) => {
let v627 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v628 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v627, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v628)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_63_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v595: Term, v596: Term, v609: Term) -> CheckResult<Term> {
let v610 = match s.builtin_core(EvalOp::Extract, &[v595, v596, v609]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v610)
}
pub(super) fn if_64_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v586 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v593 = match if_59_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v594 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v595 = match s.builtin_list(EvalOp::ListNth, &[v586, v593, v594]) { Ok(v) => v, Err(e) => return Err(e) };
let v596 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v597 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v604 = match if_60_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v605 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v606 = match s.builtin_list(EvalOp::ListNth, &[v597, v604, v605]) { Ok(v) => v, Err(e) => return Err(e) };
let v607 = match s.builtin_core(EvalOp::Length, &[v606]) { Ok(v) => v, Err(e) => return Err(e) };
let v608 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v609 = match s.builtin_core(EvalOp::Add, &[v607, v608]) { Ok(v) => v, Err(e) => return Err(e) };
more_63_eo__24eo_5fprog_5fconcat_5fcprop(s, v595, v596, v609)
}
Some(false) => {
let v611 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v618 = match if_61_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v619 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v620 = match s.builtin_list(EvalOp::ListNth, &[v611, v618, v619]) { Ok(v) => v, Err(e) => return Err(e) };
let v621 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v622 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v629 = match if_62_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v630 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v631 = match s.builtin_list(EvalOp::ListNth, &[v622, v629, v630]) { Ok(v) => v, Err(e) => return Err(e) };
let v632 = match s.builtin_core(EvalOp::Length, &[v631]) { Ok(v) => v, Err(e) => return Err(e) };
let v633 = match s.builtin_core(EvalOp::Extract, &[v620, v621, v632]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v633)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_65_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v531 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v532 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v581 = match if_58_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v582 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v532, v581]) { Ok(v) => v, Err(e) => return Err(e) };
let v583 = match eo__24str_5fflatten(s, v582) { Ok(v) => v, Err(e) => return Err(e) };
let v584 = match s.builtin_list(EvalOp::ListRev, &[v531, v583]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v584)
}
Some(false) => {
let v585 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v634 = match if_64_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v635 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v585, v634]) { Ok(v) => v, Err(e) => return Err(e) };
let v636 = match eo__24str_5fflatten(s, v635) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v636)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_66_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v641 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v642 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v643 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v642, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v644 = match s.builtin_list(EvalOp::ListRev, &[v641, v643]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v644)
}
Some(false) => {
let v645 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v646 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v645, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v646)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_67_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v655 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v656 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v657 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v656, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v658 = match s.builtin_list(EvalOp::ListRev, &[v655, v657]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v658)
}
Some(false) => {
let v659 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v660 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v659, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v660)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_68_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v638 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v639 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v640 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v647 = match if_66_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v648 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v649 = match s.builtin_list(EvalOp::ListNth, &[v640, v647, v648]) { Ok(v) => v, Err(e) => return Err(e) };
let v650 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v639, v649]) { Ok(v) => v, Err(e) => return Err(e) };
let v651 = match eo__24str_5fflatten(s, v650) { Ok(v) => v, Err(e) => return Err(e) };
let v652 = match s.builtin_list(EvalOp::ListRev, &[v638, v651]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v652)
}
Some(false) => {
let v653 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v654 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v661 = match if_67_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v662 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v663 = match s.builtin_list(EvalOp::ListNth, &[v654, v661, v662]) { Ok(v) => v, Err(e) => return Err(e) };
let v664 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v653, v663]) { Ok(v) => v, Err(e) => return Err(e) };
let v665 = match eo__24str_5fflatten(s, v664) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v665)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_69_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v684 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v685 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v686 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v685, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v687 = match s.builtin_list(EvalOp::ListRev, &[v684, v686]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v687)
}
Some(false) => {
let v688 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v689 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v688, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v689)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_70_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v697 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v698 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v699 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v698, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v700 = match s.builtin_list(EvalOp::ListRev, &[v697, v699]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v700)
}
Some(false) => {
let v701 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v702 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v701, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v702)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_71_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v712 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v713 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v714 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v713, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v715 = match s.builtin_list(EvalOp::ListRev, &[v712, v714]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v715)
}
Some(false) => {
let v716 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v717 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v716, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v717)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_72_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v723 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v724 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v725 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v724, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v726 = match s.builtin_list(EvalOp::ListRev, &[v723, v725]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v726)
}
Some(false) => {
let v727 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v728 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v727, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v728)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_73_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v737 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v738 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v739 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v738, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v740 = match s.builtin_list(EvalOp::ListRev, &[v737, v739]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v740)
}
Some(false) => {
let v741 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v742 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v741, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v742)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_74_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v748 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v749 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v750 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v749, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v751 = match s.builtin_list(EvalOp::ListRev, &[v748, v750]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v751)
}
Some(false) => {
let v752 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v753 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v752, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v753)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_75_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v720: Term, v721: Term, v734: Term) -> CheckResult<Term> {
let v735 = match s.builtin_core(EvalOp::Extract, &[v720, v721, v734]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v735)
}
pub(super) fn if_76_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v711 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v718 = match if_71_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v719 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v720 = match s.builtin_list(EvalOp::ListNth, &[v711, v718, v719]) { Ok(v) => v, Err(e) => return Err(e) };
let v721 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v722 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v729 = match if_72_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v730 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v731 = match s.builtin_list(EvalOp::ListNth, &[v722, v729, v730]) { Ok(v) => v, Err(e) => return Err(e) };
let v732 = match s.builtin_core(EvalOp::Length, &[v731]) { Ok(v) => v, Err(e) => return Err(e) };
let v733 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v734 = match s.builtin_core(EvalOp::Add, &[v732, v733]) { Ok(v) => v, Err(e) => return Err(e) };
more_75_eo__24eo_5fprog_5fconcat_5fcprop(s, v720, v721, v734)
}
Some(false) => {
let v736 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v743 = match if_73_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v744 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v745 = match s.builtin_list(EvalOp::ListNth, &[v736, v743, v744]) { Ok(v) => v, Err(e) => return Err(e) };
let v746 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v747 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v754 = match if_74_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v755 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v756 = match s.builtin_list(EvalOp::ListNth, &[v747, v754, v755]) { Ok(v) => v, Err(e) => return Err(e) };
let v757 = match s.builtin_core(EvalOp::Length, &[v756]) { Ok(v) => v, Err(e) => return Err(e) };
let v758 = match s.builtin_core(EvalOp::Extract, &[v745, v746, v757]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v758)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_77_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v765 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v766 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v767 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v766, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v768 = match s.builtin_list(EvalOp::ListRev, &[v765, v767]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v768)
}
Some(false) => {
let v769 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v770 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v769, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v770)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_78_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v776 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v777 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v778 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v777, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v779 = match s.builtin_list(EvalOp::ListRev, &[v776, v778]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v779)
}
Some(false) => {
let v780 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v781 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v780, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v781)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_79_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v790 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v791 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v792 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v791, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v793 = match s.builtin_list(EvalOp::ListRev, &[v790, v792]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v793)
}
Some(false) => {
let v794 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v795 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v794, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v795)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_80_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v801 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v802 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v803 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v802, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v804 = match s.builtin_list(EvalOp::ListRev, &[v801, v803]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v804)
}
Some(false) => {
let v805 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v806 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v805, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v806)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_81_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v773: Term, v774: Term, v787: Term) -> CheckResult<Term> {
let v788 = match s.builtin_core(EvalOp::Extract, &[v773, v774, v787]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v788)
}
pub(super) fn if_82_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v764 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v771 = match if_77_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v772 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v773 = match s.builtin_list(EvalOp::ListNth, &[v764, v771, v772]) { Ok(v) => v, Err(e) => return Err(e) };
let v774 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v775 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v782 = match if_78_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v783 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v784 = match s.builtin_list(EvalOp::ListNth, &[v775, v782, v783]) { Ok(v) => v, Err(e) => return Err(e) };
let v785 = match s.builtin_core(EvalOp::Length, &[v784]) { Ok(v) => v, Err(e) => return Err(e) };
let v786 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v787 = match s.builtin_core(EvalOp::Add, &[v785, v786]) { Ok(v) => v, Err(e) => return Err(e) };
more_81_eo__24eo_5fprog_5fconcat_5fcprop(s, v773, v774, v787)
}
Some(false) => {
let v789 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v796 = match if_79_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v797 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v798 = match s.builtin_list(EvalOp::ListNth, &[v789, v796, v797]) { Ok(v) => v, Err(e) => return Err(e) };
let v799 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v800 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v807 = match if_80_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v808 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v809 = match s.builtin_list(EvalOp::ListNth, &[v800, v807, v808]) { Ok(v) => v, Err(e) => return Err(e) };
let v810 = match s.builtin_core(EvalOp::Length, &[v809]) { Ok(v) => v, Err(e) => return Err(e) };
let v811 = match s.builtin_core(EvalOp::Extract, &[v798, v799, v810]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v811)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_83_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v709 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v710 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v759 = match if_76_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v760 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v710, v759]) { Ok(v) => v, Err(e) => return Err(e) };
let v761 = match eo__24str_5fflatten(s, v760) { Ok(v) => v, Err(e) => return Err(e) };
let v762 = match s.builtin_list(EvalOp::ListRev, &[v709, v761]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v762)
}
Some(false) => {
let v763 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v812 = match if_82_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v813 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v763, v812]) { Ok(v) => v, Err(e) => return Err(e) };
let v814 = match eo__24str_5fflatten(s, v813) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v814)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_84_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v819 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v820 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v821 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v820, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v822 = match s.builtin_list(EvalOp::ListRev, &[v819, v821]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v822)
}
Some(false) => {
let v823 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v824 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v823, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v824)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_85_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v833 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v834 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v835 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v834, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v836 = match s.builtin_list(EvalOp::ListRev, &[v833, v835]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v836)
}
Some(false) => {
let v837 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v838 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v837, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v838)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_86_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v816 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v817 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v818 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v825 = match if_84_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v826 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v827 = match s.builtin_list(EvalOp::ListNth, &[v818, v825, v826]) { Ok(v) => v, Err(e) => return Err(e) };
let v828 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v817, v827]) { Ok(v) => v, Err(e) => return Err(e) };
let v829 = match eo__24str_5fflatten(s, v828) { Ok(v) => v, Err(e) => return Err(e) };
let v830 = match s.builtin_list(EvalOp::ListRev, &[v816, v829]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v830)
}
Some(false) => {
let v831 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v832 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v839 = match if_85_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v840 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v841 = match s.builtin_list(EvalOp::ListNth, &[v832, v839, v840]) { Ok(v) => v, Err(e) => return Err(e) };
let v842 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v831, v841]) { Ok(v) => v, Err(e) => return Err(e) };
let v843 = match eo__24str_5fflatten(s, v842) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v843)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_87_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v853 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v854 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v855 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v854, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v856 = match s.builtin_list(EvalOp::ListRev, &[v853, v855]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v856)
}
Some(false) => {
let v857 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v858 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v857, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v858)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_88_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v864 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v865 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v866 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v865, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v867 = match s.builtin_list(EvalOp::ListRev, &[v864, v866]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v867)
}
Some(false) => {
let v868 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v869 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v868, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v869)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_89_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v878 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v879 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v880 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v879, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v881 = match s.builtin_list(EvalOp::ListRev, &[v878, v880]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v881)
}
Some(false) => {
let v882 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v883 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v882, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v883)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_90_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v889 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v890 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v891 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v890, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v892 = match s.builtin_list(EvalOp::ListRev, &[v889, v891]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v892)
}
Some(false) => {
let v893 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v894 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v893, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v894)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_91_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v861: Term, v862: Term, v875: Term) -> CheckResult<Term> {
let v876 = match s.builtin_core(EvalOp::Extract, &[v861, v862, v875]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v876)
}
pub(super) fn if_92_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v852 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v859 = match if_87_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v860 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v861 = match s.builtin_list(EvalOp::ListNth, &[v852, v859, v860]) { Ok(v) => v, Err(e) => return Err(e) };
let v862 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v863 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v870 = match if_88_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v871 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v872 = match s.builtin_list(EvalOp::ListNth, &[v863, v870, v871]) { Ok(v) => v, Err(e) => return Err(e) };
let v873 = match s.builtin_core(EvalOp::Length, &[v872]) { Ok(v) => v, Err(e) => return Err(e) };
let v874 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v875 = match s.builtin_core(EvalOp::Add, &[v873, v874]) { Ok(v) => v, Err(e) => return Err(e) };
more_91_eo__24eo_5fprog_5fconcat_5fcprop(s, v861, v862, v875)
}
Some(false) => {
let v877 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v884 = match if_89_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v885 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v886 = match s.builtin_list(EvalOp::ListNth, &[v877, v884, v885]) { Ok(v) => v, Err(e) => return Err(e) };
let v887 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v888 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v895 = match if_90_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v896 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v897 = match s.builtin_list(EvalOp::ListNth, &[v888, v895, v896]) { Ok(v) => v, Err(e) => return Err(e) };
let v898 = match s.builtin_core(EvalOp::Length, &[v897]) { Ok(v) => v, Err(e) => return Err(e) };
let v899 = match s.builtin_core(EvalOp::Extract, &[v886, v887, v898]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v899)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_93_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v906 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v907 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v908 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v907, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v909 = match s.builtin_list(EvalOp::ListRev, &[v906, v908]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v909)
}
Some(false) => {
let v910 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v911 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v910, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v911)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_94_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v917 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v918 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v919 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v918, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v920 = match s.builtin_list(EvalOp::ListRev, &[v917, v919]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v920)
}
Some(false) => {
let v921 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v922 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v921, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v922)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_95_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v931 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v932 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v933 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v932, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v934 = match s.builtin_list(EvalOp::ListRev, &[v931, v933]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v934)
}
Some(false) => {
let v935 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v936 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v935, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v936)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_96_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v942 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v943 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v944 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v943, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v945 = match s.builtin_list(EvalOp::ListRev, &[v942, v944]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v945)
}
Some(false) => {
let v946 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v947 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v946, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v947)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_97_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v914: Term, v915: Term, v928: Term) -> CheckResult<Term> {
let v929 = match s.builtin_core(EvalOp::Extract, &[v914, v915, v928]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v929)
}
pub(super) fn if_98_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v905 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v912 = match if_93_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v913 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v914 = match s.builtin_list(EvalOp::ListNth, &[v905, v912, v913]) { Ok(v) => v, Err(e) => return Err(e) };
let v915 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v916 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v923 = match if_94_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v924 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v925 = match s.builtin_list(EvalOp::ListNth, &[v916, v923, v924]) { Ok(v) => v, Err(e) => return Err(e) };
let v926 = match s.builtin_core(EvalOp::Length, &[v925]) { Ok(v) => v, Err(e) => return Err(e) };
let v927 = match s.literal(Lit::Numeral(Integer::from(2u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v928 = match s.builtin_core(EvalOp::Add, &[v926, v927]) { Ok(v) => v, Err(e) => return Err(e) };
more_97_eo__24eo_5fprog_5fconcat_5fcprop(s, v914, v915, v928)
}
Some(false) => {
let v930 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v937 = match if_95_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v938 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v939 = match s.builtin_list(EvalOp::ListNth, &[v930, v937, v938]) { Ok(v) => v, Err(e) => return Err(e) };
let v940 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v941 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v948 = match if_96_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v949 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v950 = match s.builtin_list(EvalOp::ListNth, &[v941, v948, v949]) { Ok(v) => v, Err(e) => return Err(e) };
let v951 = match s.builtin_core(EvalOp::Length, &[v950]) { Ok(v) => v, Err(e) => return Err(e) };
let v952 = match s.builtin_core(EvalOp::Extract, &[v939, v940, v951]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v952)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_99_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v850 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v851 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v900 = match if_92_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v901 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v851, v900]) { Ok(v) => v, Err(e) => return Err(e) };
let v902 = match eo__24str_5fflatten(s, v901) { Ok(v) => v, Err(e) => return Err(e) };
let v903 = match s.builtin_list(EvalOp::ListRev, &[v850, v902]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v903)
}
Some(false) => {
let v904 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v953 = match if_98_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v954 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v904, v953]) { Ok(v) => v, Err(e) => return Err(e) };
let v955 = match eo__24str_5fflatten(s, v954) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v955)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_100_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v960 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v961 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v962 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v961, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v963 = match s.builtin_list(EvalOp::ListRev, &[v960, v962]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v963)
}
Some(false) => {
let v964 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v965 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v964, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v965)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_101_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v974 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v975 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v976 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v975, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v977 = match s.builtin_list(EvalOp::ListRev, &[v974, v976]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v977)
}
Some(false) => {
let v978 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v979 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v978, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v979)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_102_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v957 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v958 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v959 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v966 = match if_100_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v967 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v968 = match s.builtin_list(EvalOp::ListNth, &[v959, v966, v967]) { Ok(v) => v, Err(e) => return Err(e) };
let v969 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v958, v968]) { Ok(v) => v, Err(e) => return Err(e) };
let v970 = match eo__24str_5fflatten(s, v969) { Ok(v) => v, Err(e) => return Err(e) };
let v971 = match s.builtin_list(EvalOp::ListRev, &[v957, v970]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v971)
}
Some(false) => {
let v972 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v973 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v980 = match if_101_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v981 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v982 = match s.builtin_list(EvalOp::ListNth, &[v973, v980, v981]) { Ok(v) => v, Err(e) => return Err(e) };
let v983 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v972, v982]) { Ok(v) => v, Err(e) => return Err(e) };
let v984 = match eo__24str_5fflatten(s, v983) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v984)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_185_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v849: Term, v986: Term, v848: Term, v681: Term, v680: Term, v676: Term, v672: Term, v671: Term, v670: Term, v361: Term) -> CheckResult<Term> {
let v987 = match s.builtin_core(EvalOp::Add, &[v849, v986]) { Ok(v) => v, Err(e) => return Err(e) };
let v988 = match s.apply(v848, v987) { Ok(v) => v, Err(e) => return Err(e) };
let v989 = match s.apply(v681, v988) { Ok(v) => v, Err(e) => return Err(e) };
let v990 = match s.apply(v680, v989) { Ok(v) => v, Err(e) => return Err(e) };
let v991 = match s.apply(v676, v990) { Ok(v) => v, Err(e) => return Err(e) };
let v992 = match s.apply(v672, v991) { Ok(v) => v, Err(e) => return Err(e) };
let v993 = match eo__24eo_5ftypeof(s, v992) { Ok(v) => v, Err(e) => return Err(e) };
let v994 = match eo__24eo_5fnil(s, v671, v993) { Ok(v) => v, Err(e) => return Err(e) };
let v995 = match s.apply(v670, v994) { Ok(v) => v, Err(e) => return Err(e) };
let v996 = match s.apply(v361, v995) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v996)
}
pub(super) fn more_184_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v694: Term, v706: Term, a0: Term, v4: Term, v7: Term, v693: Term, v681: Term, v680: Term, v676: Term, v672: Term, v671: Term, v670: Term, v361: Term) -> CheckResult<Term> {
let v707 = match s.apply(v694, v706) { Ok(v) => v, Err(e) => return Err(e) };
let v708 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v815 = match if_83_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v844 = match if_86_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v845 = match eo__24str_5foverlap_5frec(s, v815, v844) { Ok(v) => v, Err(e) => return Err(e) };
let v846 = match s.builtin_core(EvalOp::Add, &[v708, v845]) { Ok(v) => v, Err(e) => return Err(e) };
let v847 = match s.apply(v707, v846) { Ok(v) => v, Err(e) => return Err(e) };
let v848 = match s.apply(v693, v847) { Ok(v) => v, Err(e) => return Err(e) };
let v849 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v956 = match if_99_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v985 = match if_102_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v986 = match eo__24str_5foverlap_5frec(s, v956, v985) { Ok(v) => v, Err(e) => return Err(e) };
more_185_eo__24eo_5fprog_5fconcat_5fcprop(s, v849, v986, v848, v681, v680, v676, v672, v671, v670, v361)
}
pub(super) fn more_183_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, v4: Term, v682: Term, v7: Term, v681: Term, v680: Term, v676: Term, v672: Term, v671: Term, v670: Term, v361: Term) -> CheckResult<Term> {
let v683 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v690 = match if_69_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v691 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v692 = match s.builtin_list(EvalOp::ListNth, &[v683, v690, v691]) { Ok(v) => v, Err(e) => return Err(e) };
let v693 = match s.apply(v682, v692) { Ok(v) => v, Err(e) => return Err(e) };
let v694 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v695 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v696 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v703 = match if_70_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v704 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v705 = match s.builtin_list(EvalOp::ListNth, &[v696, v703, v704]) { Ok(v) => v, Err(e) => return Err(e) };
let v706 = match s.apply(v695, v705) { Ok(v) => v, Err(e) => return Err(e) };
more_184_eo__24eo_5fprog_5fconcat_5fcprop(s, v694, v706, a0, v4, v7, v693, v681, v680, v676, v672, v671, v670, v361)
}
pub(super) fn more_182_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v24: Term, a0: Term, v4: Term, v7: Term, v670: Term, v361: Term) -> CheckResult<Term> {
let v671 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v672 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v673 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v674 = match s.apply(v673, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v675 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v676 = match s.apply(v674, v675) { Ok(v) => v, Err(e) => return Err(e) };
let v677 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v678 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v679 = match s.apply(v678, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v680 = match s.apply(v677, v679) { Ok(v) => v, Err(e) => return Err(e) };
let v681 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v682 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_183_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4, v682, v7, v681, v680, v676, v672, v671, v670, v361)
}
pub(super) fn more_181_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, v7: Term, v496: Term, v389: Term, v388: Term, v374: Term, v4: Term, v362: Term, v24: Term, v361: Term) -> CheckResult<Term> {
let v525 = match if_52_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v526 = match eo__24str_5foverlap_5frec(s, v496, v525) { Ok(v) => v, Err(e) => return Err(e) };
let v527 = match s.builtin_core(EvalOp::Add, &[v389, v526]) { Ok(v) => v, Err(e) => return Err(e) };
let v528 = match s.apply(v388, v527) { Ok(v) => v, Err(e) => return Err(e) };
let v529 = match s.apply(v374, v528) { Ok(v) => v, Err(e) => return Err(e) };
let v530 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v637 = match if_65_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v666 = match if_68_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v667 = match eo__24str_5foverlap_5frec(s, v637, v666) { Ok(v) => v, Err(e) => return Err(e) };
let v668 = match s.builtin_core(EvalOp::Add, &[v530, v667]) { Ok(v) => v, Err(e) => return Err(e) };
let v669 = match s.apply(v529, v668) { Ok(v) => v, Err(e) => return Err(e) };
let v670 = match s.apply(v362, v669) { Ok(v) => v, Err(e) => return Err(e) };
more_182_eo__24eo_5fprog_5fconcat_5fcprop(s, v24, a0, v4, v7, v670, v361)
}
pub(super) fn more_180_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v364: Term, v371: Term, v372: Term, v363: Term, a0: Term, v4: Term, v7: Term, v362: Term, v24: Term, v361: Term) -> CheckResult<Term> {
let v373 = match s.builtin_list(EvalOp::ListNth, &[v364, v371, v372]) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v363, v373) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match if_36_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.builtin_list(EvalOp::ListNth, &[v377, v384, v385]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.apply(v376, v386) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.apply(v375, v387) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v496 = match if_49_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_181_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7, v496, v389, v388, v374, v4, v362, v24, v361)
}
pub(super) fn more_179_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v217: Term, v354: Term, v216: Term, v49: Term, v48: Term, v44: Term, v40: Term, v39: Term, a0: Term, v4: Term, v7: Term, v24: Term) -> CheckResult<Term> {
let v355 = match s.builtin_core(EvalOp::Add, &[v217, v354]) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.apply(v216, v355) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.apply(v49, v356) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.apply(v48, v357) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.apply(v44, v358) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.apply(v40, v359) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.apply(v39, v360) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match if_35_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_180_eo__24eo_5fprog_5fconcat_5fcprop(s, v364, v371, v372, v363, a0, v4, v7, v362, v24, v361)
}
pub(super) fn more_178_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v62: Term, v74: Term, a0: Term, v4: Term, v7: Term, v61: Term, v49: Term, v48: Term, v44: Term, v40: Term, v39: Term, v24: Term) -> CheckResult<Term> {
let v75 = match s.apply(v62, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match if_15_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match if_18_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match eo__24str_5foverlap_5frec(s, v183, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.builtin_core(EvalOp::Add, &[v76, v213]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v75, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v61, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match if_31_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match if_34_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match eo__24str_5foverlap_5frec(s, v324, v353) { Ok(v) => v, Err(e) => return Err(e) };
more_179_eo__24eo_5fprog_5fconcat_5fcprop(s, v217, v354, v216, v49, v48, v44, v40, v39, a0, v4, v7, v24)
}
pub(super) fn more_177_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, v4: Term, v50: Term, v7: Term, v49: Term, v48: Term, v44: Term, v40: Term, v39: Term, v24: Term) -> CheckResult<Term> {
let v51 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match if_1_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_list(EvalOp::ListNth, &[v51, v58, v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v50, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match if_2_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.builtin_list(EvalOp::ListNth, &[v64, v71, v72]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v63, v73) { Ok(v) => v, Err(e) => return Err(e) };
more_178_eo__24eo_5fprog_5fconcat_5fcprop(s, v62, v74, a0, v4, v7, v61, v49, v48, v44, v40, v39, v24)
}
pub(super) fn if_186_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v24: Term, a0: Term, v4: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v42, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_177_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4, v50, v7, v49, v48, v44, v40, v39, v24)
}
Some(false) => {
let v997 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v998 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v999 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1006 = match if_103_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1007 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1008 = match s.builtin_list(EvalOp::ListNth, &[v999, v1006, v1007]) { Ok(v) => v, Err(e) => return Err(e) };
let v1009 = match s.apply(v998, v1008) { Ok(v) => v, Err(e) => return Err(e) };
let v1010 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1011 = match s.apply(v1009, v1010) { Ok(v) => v, Err(e) => return Err(e) };
let v1012 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v1119 = match if_116_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1148 = match if_119_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
more_171_eo__24eo_5fprog_5fconcat_5fcprop(s, v1119, v1148, v1012, v1011, v997, v24, a0, v4, v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_187_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v36: Term, v24: Term, a0: Term, v4: Term, v7: Term) -> CheckResult<Term> {
if v36 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v36) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v37 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v1637 = match if_186_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v24, a0, v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1638 = match s.apply(v38, v1637) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1638)
}
pub(super) fn more_188_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v19: Term, v21: Term, v20: Term, v17: Term, a0: Term, v7: Term, v4: Term) -> CheckResult<Option<Term>> {
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v26 { return Ok(None); }
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match if_0_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_list(EvalOp::ListNth, &[v27, v34, v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v1639 = match requires_187_eo__24eo_5fprog_5fconcat_5fcprop(s, v36, v24, a0, v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1639))
}
pub(super) fn case_0_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
more_188_eo__24eo_5fprog_5fconcat_5fcprop(s, v19, v21, v20, v17, a0, v7, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_concat_cprop"
pub fn eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn more_9_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5fcprop(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_96_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econcat_5fcprop, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_9_eo__24eo_5fcmd_5fstep_5fproven(s, v14, v2, v13)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v135: Term, v140: Term, v134: Term, v133: Term, v7: Term, v132: Term, v131: Term) -> CheckResult<Term> {
let v141 = match s.apply(v135, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v134, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v133, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v132, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v145, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v131, v147) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v148)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v104: Term, v128: Term, v95: Term, v93: Term, v21: Term, v7: Term) -> CheckResult<Term> {
let v129 = match s.apply(v104, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v95, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v93, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v136, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v137, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v139, v7) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstring_5fdecompose(s, v135, v140, v134, v133, v7, v132, v131)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v105: Term, v116: Term, v21: Term, v7: Term, v104: Term, v95: Term, v93: Term) -> CheckResult<Term> {
let v117 = match s.apply(v105, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v121, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v119, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24eo_5ftypeof(s, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match eo__24eo_5fnil(s, v118, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v117, v127) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstring_5fdecompose(s, v104, v128, v95, v93, v21, v7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v21: Term, v7: Term, v104: Term, v95: Term, v93: Term) -> CheckResult<Term> {
let v105 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v110, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v113, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v109, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v106, v115) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstring_5fdecompose(s, v105, v116, v21, v7, v104, v95, v93)
}
pub(super) fn more_8_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v77: Term, v82: Term, v7: Term, v75: Term, v74: Term, v73: Term, v72: Term, v71: Term) -> CheckResult<Term> {
let v83 = match s.apply(v77, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v75, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v74, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v73, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v72, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v89, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v71, v91) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v92)
}
pub(super) fn more_7_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v23: Term, v70: Term, v21: Term, v7: Term) -> CheckResult<Term> {
let v71 = match s.apply(v23, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v7) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fstring_5fdecompose(s, v77, v82, v7, v75, v74, v73, v72, v71)
}
pub(super) fn more_6_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v21: Term, v7: Term, v58: Term, v54: Term, v53: Term, v52: Term, v39: Term, v25: Term, v23: Term) -> CheckResult<Term> {
let v59 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v58, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v54, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match eo__24eo_5ftypeof(s, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match eo__24eo_5fnil(s, v53, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v52, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v39, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v25, v69) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fstring_5fdecompose(s, v23, v70, v21, v7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v44: Term, v46: Term, v7: Term, v43: Term, v41: Term, v40: Term, v21: Term, v39: Term, v25: Term, v23: Term) -> CheckResult<Term> {
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v43, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v41, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v40, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v56, v57) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fstring_5fdecompose(s, v21, v7, v58, v54, v53, v52, v39, v25, v23)
}
pub(super) fn more_4_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v32: Term, v34: Term, v7: Term, v31: Term, v27: Term, v26: Term, v21: Term, v25: Term, v23: Term) -> CheckResult<Term> {
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v31, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v27, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v26, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v21) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fstring_5fdecompose(s, v44, v46, v7, v43, v41, v40, v21, v39, v25, v23)
}
pub(super) fn if_9_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, condition: Term, v21: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v21) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fstring_5fdecompose(s, v32, v34, v7, v31, v27, v26, v21, v25, v23)
}
Some(false) => {
let v93 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v98, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v99, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v97, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v96, v103) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5fdecompose(s, v21, v7, v104, v95, v93)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_10_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v17: Term, v14: Term, v7: Term, a0: Term) -> CheckResult<Option<Term>> {
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v14 != v7 { return Ok(None); }
let v149 = match if_9_eo__24eo_5fprog_5fstring_5fdecompose(s, a0, v21, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v149))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
let v10 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v18 { return Ok(None); }
more_10_eo__24eo_5fprog_5fstring_5fdecompose(s, v17, v14, v7, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fdecompose(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_decompose"
pub fn eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fdecompose(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn more_10_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v14: Term, v2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fstring_5fdecompose(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_97_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fdecompose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_10_eo__24eo_5fcmd_5fstep_5fproven(s, v14, v2, v13)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, v8: Term, v9: Term, v2: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if v8 != v9 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v8) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__40witness_5fstring_5flength, &[v13, a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, v5: Term, v6: Term, a2: Term, v2: Term, a1: Term) -> CheckResult<Term> {
if v5 != v6 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v5) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v7 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Gt, &[a2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s, v8, v9, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
pub(super) fn case_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Gt, &[a1, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength(s, v5, v6, a2, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn body_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_exists_string_length"
pub fn eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fexists_5fstring_5flength(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_98_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eexists_5fstring_5flength, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fexists_5fstring_5flength(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, v23: Term, v18: Term, v7: Term) -> CheckResult<Option<Term>> {
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v18, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v7, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, v11: Term, a0: Term, v10: Term, a1: Term, v9: Term, v8: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v8, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstring_5fcode_5finj(s, v23, v18, v7)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s, v11, a0, v10, a1, v9, v8, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_code_inj"
pub fn eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fcode_5finj(s, a0, a1);
s.leave();
result
}
pub(super) fn case_99_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fcode_5finj, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fstring_5fcode_5finj(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_24_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_96_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_97_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_98_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_99_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s: &mut Store, v17: Term, v11: Term, v15: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v17, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s, v17, v11, v15)
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_seq_unit_inj"
pub fn eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s, a0);
s.leave();
result
}
pub(super) fn case_100_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fseq_5funit_5finj, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fre_5finter(s: &mut Store, v18: Term, v7: Term, v4: Term, v13: Term) -> CheckResult<Option<Term>> {
let v19 = match s.apply(v18, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v9 else { return Ok(None); }
;
let v10 = fields[0];
let v11 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
if v16 != v7 { return Ok(None); }
let v18 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fre_5finter(s, v18, v7, v4, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fre_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5finter(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_inter"
pub fn eo__24eo_5fprog_5fre_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5finter(s, a0, a1);
s.leave();
result
}
pub(super) fn more_11_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match eo__24eo_5fprog_5fre_5finter(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_101_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5finter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_11_eo__24eo_5fcmd_5fstep_5fproven(s, v10, v12)
}
pub(super) fn more_0_eo__24mk_5fre_5fconcat(s: &mut Store, v12: Term, v19: Term, v9: Term, v16: Term, v2: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v21 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v29])))
}
pub(super) fn case_0_eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
let v13 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_0_eo__24mk_5fre_5fconcat(s, v12, v19, v9, v16, v2)
}
pub(super) fn case_1_eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn step_eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24mk_5fre_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fre_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24mk_5fre_5fconcat(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24mk_5fre_5fconcat(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$mk_re_concat"
pub fn eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(944), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fre_5fconcat(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(944), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_list(EvalOp::ListRev, &[v2, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24mk_5fre_5fconcat(s, v3, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5fconcat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_concat"
pub fn eo__24eo_5fprog_5fre_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5fconcat(s, a0);
s.leave();
result
}
pub(super) fn case_102_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fconcat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fmk_5fpremise_5flist(s, v2, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fpf, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fprog_5fre_5fconcat(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn more_3_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, v57: Term, v58: Term, v39: Term, v34: Term) -> CheckResult<Option<Term>> {
let v59 = match s.apply(v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v39, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v34, v60) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v61))
}
pub(super) fn more_2_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, v46: Term, v19: Term, v26: Term, v45: Term, v43: Term, v41: Term, v2: Term, v40: Term, v39: Term, v34: Term) -> CheckResult<Option<Term>> {
let v47 = match s.apply(v46, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v47, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v45, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v43, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v41, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v40, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24mk_5fre_5funfold_5fpos_5fstar(s, v57, v58, v39, v34)
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, v12: Term, v19: Term, v26: Term, v2: Term, v34: Term) -> CheckResult<Option<Term>> {
let v35 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fre_5funfold_5fpos_5fstar(s, v46, v19, v26, v45, v43, v41, v2, v40, v39, v34)
}
pub(super) fn more_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, v16: Term, a0: Term, a1: Term, v12: Term, v19: Term, v2: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v28 { return Ok(None); }
let v29 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v29, v33) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, a1, v12, v19, v26, v2, v34)
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s, v16, a0, a1, v12, v19, v2)
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_pos_star"
pub fn eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_2_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, v22: Term, v26: Term, v16: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v22, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v16, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
// EO program "$re_unfold_pos_concat_rec"
pub fn eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(972), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(972), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Add, &[a3, v14]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v15, v13, v11, a3)
}
pub(super) fn case_2_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40re_5funfold_5fpos_5fcomponent, &[a0, a2, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[a3, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24pair_5ffirst(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24re_5funfold_5fpos_5fconcat_5frec(s, v10, v14, v7, a0, a2, a3, v5, v2)
}
pub(super) fn more_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, v2: Term, a2: Term, v15: Term, v13: Term, v11: Term, a3: Term) -> CheckResult<Option<Term>> {
let v16 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24pair_5ffirst(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v11, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Add, &[a3, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24pair_5fsecond(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn more_1_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, v10: Term, v14: Term, v7: Term, a0: Term, a2: Term, a3: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v7, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__40re_5funfold_5fpos_5fcomponent, &[a0, a2, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::Add, &[a3, v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24pair_5fsecond(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24re_5funfold_5fpos_5fconcat_5frec(s, v22, v26, v16)
}
pub(super) fn more_3_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v42: Term, v48: Term, v41: Term, v37: Term, a0: Term, v29: Term, v2: Term) -> CheckResult<Option<Term>> {
let v49 = match s.apply(v42, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v50, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v49, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v41, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v37, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v29, v55, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, v2, v57) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn more_2_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v30: Term, v36: Term, v2: Term, a0: Term, v29: Term) -> CheckResult<Option<Term>> {
let v37 = match s.apply(v30, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v44, v47) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24mk_5fre_5funfold_5fpos(s, v42, v48, v41, v37, a0, v29, v2)
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v24: Term, v23: Term, v15: Term, v11: Term, v2: Term, a0: Term) -> CheckResult<Option<Term>> {
let v25 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v15, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v11, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v32, v35) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fre_5funfold_5fpos(s, v30, v36, v2, a0, v29)
}
pub(super) fn more_0_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v2: Term, v12: Term, v11: Term, a0: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fpos(s, v24, v23, v15, v11, v2, a0)
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fre_5funfold_5fpos(s, v2, v12, v11, a0)
}
pub(super) fn more_4_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v32: Term, v41: Term, v30: Term, v5: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let v42 = match s.apply(v32, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v30, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v46, v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24pair_5fsecond(s, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v43, v52) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v53)
}
pub(super) fn if_5_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, condition: Term, a0: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v22, v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24pair_5ffirst(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v19, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
Some(false) => {
let v30 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v35, v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24pair_5ffirst(s, v40) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24mk_5fre_5funfold_5fpos(s, v32, v41, v30, v5, v2, a0)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_6_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v14: Term, a0: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match eo__24pair_5fsecond(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Eq, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match if_5_eo__24mk_5fre_5funfold_5fpos(s, v17, a0, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v54))
}
pub(super) fn case_1_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v10 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v9, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24mk_5fre_5funfold_5fpos(s, v14, a0, v5, v2)
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fre_5funfold_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_pos"
pub fn eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fpos(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5funfold_5fpos(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match eo__24mk_5fre_5funfold_5fpos(s, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5funfold_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5funfold_5fpos(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_unfold_pos"
pub fn eo__24eo_5fprog_5fre_5funfold_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5funfold_5fpos(s, a0);
s.leave();
result
}
pub(super) fn case_103_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funfold_5fpos, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fre_5funfold_5fpos(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_0_25_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_100_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_101_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_102_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_103_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, condition: Term, v8: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListRev, &[v13, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_2_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_3_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.builtin_core(EvalOp::Length, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$str_fixed_len_re"
pub fn eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1059), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5ffixed_5flen_5fre(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1059), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24str_5ffixed_5flen_5fre(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_4_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_1_eo__24str_5ffixed_5flen_5fre(s, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_5_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_3_eo__24str_5ffixed_5flen_5fre(s, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn cases_0_0_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24str_5ffixed_5flen_5fre(s: &mut Store, v10: Term, v11: Term, v5: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
pub(super) fn if_1_eo__24str_5ffixed_5flen_5fre(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24str_5ffixed_5flen_5fre(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match requires_0_eo__24str_5ffixed_5flen_5fre(s, v10, v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_2_eo__24str_5ffixed_5flen_5fre(s: &mut Store, v10: Term, v11: Term, v5: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
pub(super) fn if_3_eo__24str_5ffixed_5flen_5fre(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24str_5ffixed_5flen_5fre(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match requires_2_eo__24str_5ffixed_5flen_5fre(s, v10, v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, v5: Term, v74: Term, v70: Term, v66: Term, v2: Term, v65: Term, v64: Term, v63: Term) -> CheckResult<Term> {
let v75 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v74, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v70, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v66, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.builtin_list(EvalOp::ListSingletonElim, &[v79, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v65, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v64, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v83, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v63, v85) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v86)
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, v51: Term, v62: Term, a0: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let v63 = match s.apply(v51, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v68, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v72, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v71, v73) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v5, v74, v70, v66, v2, v65, v64, v63)
}
pub(super) fn if_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v41 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_list(EvalOp::ListRev, &[v41, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
Some(false) => {
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, v39: Term, v44: Term, v26: Term, v25: Term, v24: Term) -> CheckResult<Term> {
let v45 = match s.apply(v39, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v26, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v25, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v24, v49) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v50)
}
pub(super) fn more_4_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, v29: Term, v30: Term, a0: Term, v5: Term, v27: Term, a2: Term, v2: Term, v26: Term, v25: Term, v24: Term) -> CheckResult<Term> {
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v31, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v27, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match if_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_list(EvalOp::ListSingletonElim, &[v40, v43]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v39, v44, v26, v25, v24)
}
pub(super) fn more_3_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, v5: Term, v18: Term, v9: Term, v8: Term, v7: Term, a0: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let v19 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v9, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v8, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v7, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v29, v30, a0, v5, v27, a2, v2, v26, v25, v24)
}
pub(super) fn if_6_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v5, v18, v9, v8, v7, a0, a2, v2)
}
Some(false) => {
let v51 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v55, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v53, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v52, v61) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v51, v62, a0, v5, v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v87 = match if_6_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a2, a0, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v87))
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_neg_concat_fixed"
pub fn eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v15 = match if_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v11, v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_unfold_neg_concat_fixed"
pub fn eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1);
s.leave();
result
}
pub(super) fn case_104_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_6_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v21: Term, v84: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v85 = match s.apply(v21, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v12, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v86, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v11, v88) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v89))
}
pub(super) fn more_5_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v64: Term, v72: Term, v58: Term, v2: Term, v57: Term, v56: Term, v55: Term, v40: Term, v30: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v73 = match s.apply(v64, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v58, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v74, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v57, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v56, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v79, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v55, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v40, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v30, v83) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24mk_5fre_5funfold_5fneg(s, v21, v84, v12, v11)
}
pub(super) fn more_4_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v60: Term, a0: Term, v58: Term, v2: Term, v57: Term, v56: Term, v55: Term, v40: Term, v30: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v61 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__24emb_5fVar, &[v61, v62]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v60, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v65, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__24emb_5fVar, &[v69, v70]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v68, v71) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24mk_5fre_5funfold_5fneg(s, v64, v72, v58, v2, v57, v56, v55, v40, v30, v21, v12, v11)
}
pub(super) fn more_3_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v48: Term, v47: Term, v43: Term, v2: Term, v42: Term, v41: Term, a0: Term, v40: Term, v30: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v49 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__24emb_5fVar, &[v48, v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v47, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v43, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v42, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v41, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24mk_5fre_5funfold_5fneg(s, v60, a0, v58, v2, v57, v56, v55, v40, v30, v21, v12, v11)
}
pub(super) fn more_2_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v36: Term, v35: Term, v31: Term, a0: Term, v2: Term, v30: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v37 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__24emb_5fVar, &[v36, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v31, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24mk_5fre_5funfold_5fneg(s, v48, v47, v43, v2, v42, v41, a0, v40, v30, v21, v12, v11)
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v24: Term, v23: Term, v22: Term, a0: Term, v2: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v25 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24emb_5fVar, &[v24, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v22, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fre_5funfold_5fneg(s, v36, v35, v31, a0, v2, v30, v21, v12, v11)
}
pub(super) fn more_0_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, v2: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24emb_5fVar, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v13, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fneg(s, v24, v23, v22, a0, v2, v21, v12, v11)
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fre_5funfold_5fneg(s, a0, v2, v12, v11)
}
pub(super) fn more_12_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v73: Term, v74: Term, v49: Term, v34: Term, v24: Term, v15: Term) -> CheckResult<Option<Term>> {
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v49, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v34, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v24, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v15, v78) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v79))
}
pub(super) fn more_11_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v62: Term, v58: Term, v52: Term, v2: Term, v51: Term, v50: Term, v49: Term, v34: Term, v24: Term, v15: Term) -> CheckResult<Option<Term>> {
let v63 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__24emb_5fVar, &[v63, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v62, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v58, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v52, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_list(EvalOp::ListSingletonElim, &[v69, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v51, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v50, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24mk_5fre_5funfold_5fneg(s, v73, v74, v49, v34, v24, v15)
}
pub(super) fn more_10_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, v2: Term, v50: Term, v49: Term, v34: Term, v24: Term, v15: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__24emb_5fVar, &[v55, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v54, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24mk_5fre_5funfold_5fneg(s, v62, v58, v52, v2, v51, v50, v49, v34, v24, v15)
}
pub(super) fn more_9_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v38: Term, a0: Term, v37: Term, v5: Term, v36: Term, v35: Term, v2: Term, v34: Term, v24: Term, v15: Term) -> CheckResult<Option<Term>> {
let v39 = match s.apply(v38, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__24emb_5fVar, &[v42, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v41, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v37, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v36, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v35, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24mk_5fre_5funfold_5fneg(s, a0, v2, v50, v49, v34, v24, v15)
}
pub(super) fn more_8_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, v26: Term, v25: Term, v5: Term, v2: Term, v24: Term, v15: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24emb_5fVar, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v25, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24mk_5fre_5funfold_5fneg(s, v38, a0, v37, v5, v36, v35, v2, v34, v24, v15)
}
pub(super) fn more_7_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v7: Term, v14: Term, a0: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v7, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24emb_5fVar, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v16, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24mk_5fre_5funfold_5fneg(s, a0, v26, v25, v5, v2, v24, v15)
}
pub(super) fn case_1_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fVar, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24mk_5fre_5funfold_5fneg(s, v7, v14, a0, v5, v2)
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fre_5funfold_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_neg"
pub fn eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fneg(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5funfold_5fneg(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match eo__24mk_5fre_5funfold_5fneg(s, v11, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5funfold_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5funfold_5fneg(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_unfold_neg"
pub fn eo__24eo_5fprog_5fre_5funfold_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5funfold_5fneg(s, a0);
s.leave();
result
}
pub(super) fn case_105_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funfold_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fre_5funfold_5fneg(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_3_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, v40: Term, v52: Term, v31: Term, v24: Term, v23: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v40, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v31, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v24, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v55, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v23, v57) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn more_2_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, v11: Term, v8: Term, v40: Term, v31: Term, v24: Term, v23: Term) -> CheckResult<Option<Term>> {
let v41 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v42, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v41, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v50, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstring_5fext(s, v40, v52, v31, v24, v23)
}
pub(super) fn more_0_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, v6: Term, v11: Term, a1: Term, a2: Term, v5: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v6, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v12, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v5, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5fmk_5fext_5fdeq(s, v6, v11, a1, a2, v5)
}
pub(super) fn more_1_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, v9: Term, v12: Term, v4: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v4, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_1_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5fmk_5fext_5fdeq(s, v9, v12, v4)
}
pub(super) fn body_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fmk_5fext_5fdeq(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmk_5fext_5fdeq(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_mk_ext_deq"
pub fn eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fmk_5fext_5fdeq(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_1_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, v11: Term, v8: Term, v28: Term, v25: Term, v24: Term, v23: Term) -> CheckResult<Option<Term>> {
let v29 = match eo__24eo_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24str_5fmk_5fext_5fdeq(s, v11, v8, v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v25, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v32, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstring_5fext(s, v11, v8, v40, v31, v24, v23)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, v16: Term, v11: Term, v15: Term, v8: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v16, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstring_5fext(s, v11, v8, v28, v25, v24, v23)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5fext(s, v16, v11, v15, v8, v14, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fext(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_ext"
pub fn eo__24eo_5fprog_5fstring_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fext(s, a0);
s.leave();
result
}
pub(super) fn case_106_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fext, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fstring_5fext(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5freduction(s: &mut Store, v5: Term, v14: Term) -> CheckResult<Term> {
let v15 = match s.apply(v5, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
pub(super) fn more_4_eo__24str_5freduction_5fpred(s: &mut Store, v60: Term, v62: Term, v54: Term, v2: Term, v53: Term, v52: Term, v51: Term, v34: Term, v23: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v63 = match s.apply(v60, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v54, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v53, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v52, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v51, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v34, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v23, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v14, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v13, v73) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v74))
}
pub(super) fn more_3_eo__24str_5freduction_5fpred(s: &mut Store, v35: Term, v50: Term, v5: Term, v2: Term, v34: Term, v23: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v51 = match s.apply(v35, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__24emb_5fVar, &[v57, v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v56, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24str_5freduction_5fpred(s, v60, v62, v54, v2, v53, v52, v51, v34, v23, v14, v13)
}
pub(super) fn more_2_eo__24str_5freduction_5fpred(s: &mut Store, v38: Term, v37: Term, v5: Term, v2: Term, v36: Term, v35: Term, v34: Term, v23: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v39 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__24emb_5fVar, &[v38, v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v37, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v42, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v41, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v36, v49) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24str_5freduction_5fpred(s, v35, v50, v5, v2, v34, v23, v14, v13)
}
pub(super) fn more_1_eo__24str_5freduction_5fpred(s: &mut Store, v26: Term, v25: Term, v24: Term, v5: Term, v2: Term, v23: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v27 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24emb_5fVar, &[v27, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v30, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v25, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v24, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24str_5freduction_5fpred(s, v38, v37, v5, v2, v36, v35, v34, v23, v14, v13)
}
pub(super) fn more_0_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24emb_5fVar, &[v17, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v15, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5freduction_5fpred(s, v26, v25, v24, v5, v2, v23, v14, v13)
}
pub(super) fn case_0_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5freduction_5fpred(s, v5, v2, v14, v13)
}
pub(super) fn more_22_eo__24str_5freduction_5fpred(s: &mut Store, v220: Term, v219: Term, v211: Term) -> CheckResult<Option<Term>> {
let v221 = match eo__24seq_5fempty(s, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v219, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v211, v222) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v223))
}
pub(super) fn more_21_eo__24str_5freduction_5fpred(s: &mut Store, v110: Term, v208: Term, v96: Term, v34: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v209 = match s.apply(v110, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v96, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v34, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v214, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v215, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v216, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v213, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v212, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24str_5freduction_5fpred(s, v220, v219, v211)
}
pub(super) fn more_20_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v196: Term, v195: Term, v194: Term, v193: Term, v192: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v197 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v197, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v198, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v199, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v196, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v195, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v194, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v203, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v193, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v205, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.apply(v192, v207) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24str_5freduction_5fpred(s, v110, v208, v96, v34, v8, v5, v2)
}
pub(super) fn more_19_eo__24str_5freduction_5fpred(s: &mut Store, v157: Term, v184: Term, v156: Term, v155: Term, v111: Term, v8: Term, v5: Term, v2: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v185 = match s.apply(v157, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v185, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v156, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v188, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v155, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v111, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24str_5freduction_5fpred(s, v8, v5, v2, v196, v195, v194, v193, v192, v110, v96, v34)
}
pub(super) fn more_18_eo__24str_5freduction_5fpred(s: &mut Store, v170: Term, v172: Term, v5: Term, v2: Term, v169: Term, v159: Term, v158: Term, v157: Term, v156: Term, v155: Term, v111: Term, v8: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v173 = match s.apply(v170, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v174, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v176, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v177, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v175, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v173, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v169, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v159, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v158, v183) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24str_5freduction_5fpred(s, v157, v184, v156, v155, v111, v8, v5, v2, v110, v96, v34)
}
pub(super) fn more_17_eo__24str_5freduction_5fpred(s: &mut Store, v160: Term, v8: Term, v5: Term, v2: Term, v159: Term, v158: Term, v157: Term, v156: Term, v155: Term, v111: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v161 = match s.apply(v160, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v162, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v164, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v165, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v163, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v161, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24str_5freduction_5fpred(s, v170, v172, v5, v2, v169, v159, v158, v157, v156, v155, v111, v8, v110, v96, v34)
}
pub(super) fn more_16_eo__24str_5freduction_5fpred(s: &mut Store, v148: Term, v2: Term, v147: Term, v145: Term, v141: Term, v112: Term, v8: Term, v5: Term, v111: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v149 = match s.apply(v148, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v149, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v147, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v145, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v141, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v112, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24str_5freduction_5fpred(s, v160, v8, v5, v2, v159, v158, v157, v156, v155, v111, v110, v96, v34)
}
pub(super) fn more_15_eo__24str_5freduction_5fpred(s: &mut Store, v129: Term, v136: Term, v125: Term, v115: Term, v114: Term, v113: Term, v8: Term, v5: Term, v2: Term, v112: Term, v111: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v137 = match s.apply(v129, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v125, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v115, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v114, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v113, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v142, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v146, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24str_5freduction_5fpred(s, v148, v2, v147, v145, v141, v112, v8, v5, v111, v110, v96, v34)
}
pub(super) fn more_14_eo__24str_5freduction_5fpred(s: &mut Store, v117: Term, v124: Term, v8: Term, v5: Term, v2: Term, v115: Term, v114: Term, v113: Term, v112: Term, v111: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v117, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v127, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v126, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v132, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v133, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v131, v135) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24str_5freduction_5fpred(s, v129, v136, v125, v115, v114, v113, v8, v5, v2, v112, v111, v110, v96, v34)
}
pub(super) fn more_13_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v112: Term, v111: Term, v110: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v113 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v116, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v118, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v121, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v119, v123) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24str_5freduction_5fpred(s, v117, v124, v8, v5, v2, v115, v114, v113, v112, v111, v110, v96, v34)
}
pub(super) fn more_12_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v100: Term, v99: Term, v98: Term, v97: Term, v2: Term, v96: Term, v34: Term) -> CheckResult<Option<Term>> {
let v101 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v102, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v100, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v99, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v98, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v97, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24str_5freduction_5fpred(s, v8, v5, v2, v112, v111, v110, v96, v34)
}
pub(super) fn more_11_eo__24str_5freduction_5fpred(s: &mut Store, v83: Term, v88: Term, v82: Term, v81: Term, v54: Term, v46: Term, v37: Term, v35: Term, v8: Term, v5: Term, v2: Term, v34: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v83, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match eo__24eo_5ftypeof(s, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match eo__24eo_5fnil(s, v82, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v81, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v54, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v46, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v37, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v35, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24str_5freduction_5fpred(s, v8, v5, v100, v99, v98, v97, v2, v96, v34)
}
pub(super) fn more_10_eo__24str_5freduction_5fpred(s: &mut Store, v72: Term, v76: Term, v70: Term, v66: Term, v56: Term, v55: Term, v8: Term, v5: Term, v54: Term, v46: Term, v37: Term, v35: Term, v2: Term, v34: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v72, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v70, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v66, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v56, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v55, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v85, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24str_5freduction_5fpred(s, v83, v88, v82, v81, v54, v46, v37, v35, v8, v5, v2, v34)
}
pub(super) fn more_9_eo__24str_5freduction_5fpred(s: &mut Store, v60: Term, v64: Term, v58: Term, v8: Term, v5: Term, v2: Term, v56: Term, v55: Term, v54: Term, v46: Term, v37: Term, v35: Term, v34: Term) -> CheckResult<Option<Term>> {
let v65 = match s.apply(v60, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v58, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v74, v75) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24str_5freduction_5fpred(s, v72, v76, v70, v66, v56, v55, v8, v5, v54, v46, v37, v35, v2, v34)
}
pub(super) fn more_8_eo__24str_5freduction_5fpred(s: &mut Store, v48: Term, v52: Term, v47: Term, v8: Term, v5: Term, v2: Term, v46: Term, v37: Term, v35: Term, v34: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v48, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v47, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24str_5freduction_5fpred(s, v60, v64, v58, v8, v5, v2, v56, v55, v54, v46, v37, v35, v34)
}
pub(super) fn more_7_eo__24str_5freduction_5fpred(s: &mut Store, v40: Term, v8: Term, v5: Term, v39: Term, v38: Term, v2: Term, v37: Term, v35: Term, v34: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v40, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v39, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v38, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24str_5freduction_5fpred(s, v48, v52, v47, v8, v5, v2, v46, v37, v35, v34)
}
pub(super) fn more_6_eo__24str_5freduction_5fpred(s: &mut Store, v24: Term, v28: Term, v23: Term, v16: Term, v10: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v24, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v23, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v16, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v10, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24str_5freduction_5fpred(s, v40, v8, v5, v39, v38, v2, v37, v35, v34)
}
pub(super) fn more_5_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v16: Term, v10: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v17, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24str_5freduction_5fpred(s, v24, v28, v23, v16, v10, v8, v5, v2)
}
pub(super) fn case_1_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24str_5freduction_5fpred(s, v8, v5, v2, v16, v10)
}
pub(super) fn more_55_eo__24str_5freduction_5fpred(s: &mut Store, v368: Term, v400: Term, v367: Term, v365: Term, v357: Term, v356: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v401 = match s.apply(v368, v400) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.apply(v401, v402) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.apply(v367, v403) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.apply(v365, v404) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.apply(v357, v405) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.apply(v406, v407) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.apply(v356, v408) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.apply(v269, v409) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.apply(v72, v410) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.apply(v55, v411) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v412))
}
pub(super) fn more_54_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v388: Term, v2: Term, v387: Term, v384: Term, v5: Term, v383: Term, v370: Term, v369: Term, v368: Term, v367: Term, v365: Term, v357: Term, v356: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v389 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.apply(v389, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.apply(v388, v390) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.apply(v391, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.apply(v387, v392) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.apply(v384, v393) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.apply(v394, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v395, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.apply(v383, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.apply(v370, v398) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.apply(v369, v399) { Ok(v) => v, Err(e) => return Err(e) };
more_55_eo__24str_5freduction_5fpred(s, v368, v400, v367, v365, v357, v356, v269, v72, v55)
}
pub(super) fn more_53_eo__24str_5freduction_5fpred(s: &mut Store, v376: Term, v8: Term, v375: Term, v2: Term, v374: Term, v371: Term, v5: Term, v370: Term, v369: Term, v368: Term, v367: Term, v365: Term, v357: Term, v356: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v377 = match s.apply(v376, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.apply(v375, v377) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.apply(v378, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.apply(v374, v379) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.apply(v371, v380) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.apply(v381, v382) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.apply(v385, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.apply(v386, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_54_eo__24str_5freduction_5fpred(s, v8, v388, v2, v387, v384, v5, v383, v370, v369, v368, v367, v365, v357, v356, v269, v72, v55)
}
pub(super) fn more_52_eo__24str_5freduction_5fpred(s: &mut Store, v358: Term, v364: Term, v2: Term, v8: Term, v5: Term, v357: Term, v356: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v365 = match s.apply(v358, v364) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.apply(v366, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v372, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v373, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_53_eo__24str_5freduction_5fpred(s, v376, v8, v375, v2, v374, v371, v5, v370, v369, v368, v367, v365, v357, v356, v269, v72, v55)
}
pub(super) fn more_51_eo__24str_5freduction_5fpred(s: &mut Store, v272: Term, v352: Term, v5: Term, v271: Term, v270: Term, v8: Term, v2: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v353 = match s.apply(v272, v352) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.apply(v353, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.apply(v271, v354) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.apply(v270, v355) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.apply(v360, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.apply(v361, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.apply(v362, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.apply(v359, v363) { Ok(v) => v, Err(e) => return Err(e) };
more_52_eo__24str_5freduction_5fpred(s, v358, v364, v2, v8, v5, v357, v356, v269, v72, v55)
}
pub(super) fn more_50_eo__24str_5freduction_5fpred(s: &mut Store, v340: Term, v2: Term, v336: Term, v333: Term, v5: Term, v332: Term, v319: Term, v318: Term, v317: Term, v304: Term, v272: Term, v271: Term, v270: Term, v8: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v341 = match s.apply(v340, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.apply(v336, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v333, v342) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.apply(v343, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.apply(v344, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v332, v346) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.apply(v319, v347) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match eo__24eo_5ftypeof(s, v348) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match eo__24eo_5fnil(s, v318, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.apply(v317, v350) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v304, v351) { Ok(v) => v, Err(e) => return Err(e) };
more_51_eo__24str_5freduction_5fpred(s, v272, v352, v5, v271, v270, v8, v2, v269, v72, v55)
}
pub(super) fn more_49_eo__24str_5freduction_5fpred(s: &mut Store, v323: Term, v328: Term, v320: Term, v8: Term, v2: Term, v5: Term, v319: Term, v318: Term, v317: Term, v304: Term, v272: Term, v271: Term, v270: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v329 = match s.apply(v323, v328) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v320, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v330, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v334, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v335, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.apply(v338, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v337, v339) { Ok(v) => v, Err(e) => return Err(e) };
more_50_eo__24str_5freduction_5fpred(s, v340, v2, v336, v333, v5, v332, v319, v318, v317, v304, v272, v271, v270, v8, v269, v72, v55)
}
pub(super) fn more_48_eo__24str_5freduction_5fpred(s: &mut Store, v305: Term, v316: Term, v8: Term, v2: Term, v5: Term, v304: Term, v272: Term, v271: Term, v270: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v317 = match s.apply(v305, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v321, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.apply(v322, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v325, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.apply(v324, v326) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v327, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_49_eo__24str_5freduction_5fpred(s, v323, v328, v320, v8, v2, v5, v319, v318, v317, v304, v272, v271, v270, v269, v72, v55)
}
pub(super) fn more_47_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v8: Term, v2: Term, v304: Term, v272: Term, v271: Term, v270: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v305 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v306, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v307, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v311, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.apply(v310, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v313, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v309, v315) { Ok(v) => v, Err(e) => return Err(e) };
more_48_eo__24str_5freduction_5fpred(s, v305, v316, v8, v2, v5, v304, v272, v271, v270, v269, v72, v55)
}
pub(super) fn more_46_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v292: Term, v2: Term, v291: Term, v288: Term, v5: Term, v287: Term, v274: Term, v273: Term, v272: Term, v271: Term, v270: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v293 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v293, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v292, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v295, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v291, v296) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v288, v297) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.apply(v298, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v299, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v287, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v274, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v273, v303) { Ok(v) => v, Err(e) => return Err(e) };
more_47_eo__24str_5freduction_5fpred(s, v5, v8, v2, v304, v272, v271, v270, v269, v72, v55)
}
pub(super) fn more_45_eo__24str_5freduction_5fpred(s: &mut Store, v280: Term, v8: Term, v279: Term, v2: Term, v278: Term, v275: Term, v5: Term, v274: Term, v273: Term, v272: Term, v271: Term, v270: Term, v269: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v281 = match s.apply(v280, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v279, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v282, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.apply(v278, v283) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.apply(v275, v284) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v285, v286) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v289, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v290, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_46_eo__24str_5freduction_5fpred(s, v8, v292, v2, v291, v288, v5, v287, v274, v273, v272, v271, v270, v269, v72, v55)
}
pub(super) fn more_44_eo__24str_5freduction_5fpred(s: &mut Store, v73: Term, v268: Term, v8: Term, v2: Term, v5: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v269 = match s.apply(v73, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v276, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v277, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_45_eo__24str_5freduction_5fpred(s, v280, v8, v279, v2, v278, v275, v5, v274, v273, v272, v271, v270, v269, v72, v55)
}
pub(super) fn more_43_eo__24str_5freduction_5fpred(s: &mut Store, v247: Term, v256: Term, v5: Term, v246: Term, v233: Term, v232: Term, v231: Term, v118: Term, v116: Term, v84: Term, v73: Term, v8: Term, v2: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v257 = match s.apply(v247, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v257, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v258, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v246, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v233, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match eo__24eo_5ftypeof(s, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match eo__24eo_5fnil(s, v232, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v231, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v118, v265) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v116, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v84, v267) { Ok(v) => v, Err(e) => return Err(e) };
more_44_eo__24str_5freduction_5fpred(s, v73, v268, v8, v2, v5, v72, v55)
}
pub(super) fn more_42_eo__24str_5freduction_5fpred(s: &mut Store, v244: Term, v8: Term, v2: Term, v5: Term, v233: Term, v232: Term, v231: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v245 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v244, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v248, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v249, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v252, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v251, v253) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v254, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v250, v255) { Ok(v) => v, Err(e) => return Err(e) };
more_43_eo__24str_5freduction_5fpred(s, v247, v256, v5, v246, v233, v232, v231, v118, v116, v84, v73, v8, v2, v72, v55)
}
pub(super) fn more_41_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v5: Term, v232: Term, v231: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v233 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v235, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v236, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v239, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v238, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v241, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v237, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v234, v243) { Ok(v) => v, Err(e) => return Err(e) };
more_42_eo__24str_5freduction_5fpred(s, v244, v8, v2, v5, v233, v232, v231, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_40_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v220: Term, v186: Term, v173: Term, v120: Term, v119: Term, v8: Term, v2: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v221 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v222, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v221, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v224, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.apply(v220, v226) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v186, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v173, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v120, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v119, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_41_eo__24str_5freduction_5fpred(s, v8, v2, v5, v232, v231, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_39_eo__24str_5freduction_5fpred(s: &mut Store, v208: Term, v8: Term, v207: Term, v2: Term, v206: Term, v203: Term, v5: Term, v202: Term, v189: Term, v188: Term, v187: Term, v186: Term, v173: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v209 = match s.apply(v208, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v207, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v210, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v206, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v203, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v213, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v214, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v202, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v189, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v188, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v187, v219) { Ok(v) => v, Err(e) => return Err(e) };
more_40_eo__24str_5freduction_5fpred(s, v5, v220, v186, v173, v120, v119, v8, v2, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_38_eo__24str_5freduction_5fpred(s: &mut Store, v194: Term, v196: Term, v2: Term, v193: Term, v190: Term, v8: Term, v5: Term, v189: Term, v188: Term, v187: Term, v186: Term, v173: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v197 = match s.apply(v194, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v197, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v193, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v190, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v200, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v205, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_39_eo__24str_5freduction_5fpred(s, v208, v8, v207, v2, v206, v203, v5, v202, v189, v188, v187, v186, v173, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_37_eo__24str_5freduction_5fpred(s: &mut Store, v175: Term, v184: Term, v174: Term, v8: Term, v2: Term, v5: Term, v173: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v185 = match s.apply(v175, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v174, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v191, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v192, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v195, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_38_eo__24str_5freduction_5fpred(s, v194, v196, v2, v193, v190, v8, v5, v189, v188, v187, v186, v173, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_36_eo__24str_5freduction_5fpred(s: &mut Store, v131: Term, v172: Term, v8: Term, v2: Term, v5: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v173 = match s.apply(v131, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v176, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v177, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v180, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v179, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v182, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v178, v183) { Ok(v) => v, Err(e) => return Err(e) };
more_37_eo__24str_5freduction_5fpred(s, v175, v184, v174, v8, v2, v5, v173, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_35_eo__24str_5freduction_5fpred(s: &mut Store, v159: Term, v160: Term, v147: Term, v134: Term, v133: Term, v132: Term, v5: Term, v131: Term, v8: Term, v2: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v161 = match s.apply(v159, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v147, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v134, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v133, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v132, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v167, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v166, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v169, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v165, v171) { Ok(v) => v, Err(e) => return Err(e) };
more_36_eo__24str_5freduction_5fpred(s, v131, v172, v8, v2, v5, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_34_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v148: Term, v5: Term, v147: Term, v134: Term, v133: Term, v132: Term, v131: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v149 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v150, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v153, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v152, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v151, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v148, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v158, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_35_eo__24str_5freduction_5fpred(s, v159, v160, v147, v134, v133, v132, v5, v131, v8, v2, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_33_eo__24str_5freduction_5fpred(s: &mut Store, v136: Term, v8: Term, v2: Term, v135: Term, v5: Term, v134: Term, v133: Term, v132: Term, v131: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v137 = match s.apply(v136, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v140, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v139, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v142, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v138, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v135, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v145, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_34_eo__24str_5freduction_5fpred(s, v8, v2, v148, v5, v147, v134, v133, v132, v131, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_32_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v124: Term, v121: Term, v5: Term, v120: Term, v119: Term, v118: Term, v116: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v125 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v125, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v124, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v121, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_33_eo__24str_5freduction_5fpred(s, v136, v8, v2, v135, v5, v134, v133, v132, v131, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_31_eo__24str_5freduction_5fpred(s: &mut Store, v111: Term, v112: Term, v99: Term, v86: Term, v85: Term, v5: Term, v8: Term, v2: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v111, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v99, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v86, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v85, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_32_eo__24str_5freduction_5fpred(s, v8, v2, v124, v121, v5, v120, v119, v118, v116, v84, v73, v72, v55)
}
pub(super) fn more_30_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v100: Term, v5: Term, v99: Term, v86: Term, v85: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v101 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v104, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v103, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v100, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24str_5freduction_5fpred(s, v111, v112, v99, v86, v85, v5, v8, v2, v84, v73, v72, v55)
}
pub(super) fn more_29_eo__24str_5freduction_5fpred(s: &mut Store, v88: Term, v8: Term, v2: Term, v87: Term, v5: Term, v86: Term, v85: Term, v84: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v88, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v91, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v90, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v87, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v97, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24str_5freduction_5fpred(s, v8, v2, v100, v5, v99, v86, v85, v84, v73, v72, v55)
}
pub(super) fn more_28_eo__24str_5freduction_5fpred(s: &mut Store, v76: Term, v2: Term, v8: Term, v74: Term, v5: Term, v73: Term, v72: Term, v55: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v76, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v77, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v74, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24str_5freduction_5fpred(s, v88, v8, v2, v87, v5, v86, v85, v84, v73, v72, v55)
}
pub(super) fn more_27_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v64: Term, v63: Term, v62: Term, v55: Term) -> CheckResult<Option<Term>> {
let v65 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v64, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v63, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v62, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24str_5freduction_5fpred(s, v76, v2, v8, v74, v5, v73, v72, v55)
}
pub(super) fn more_26_eo__24str_5freduction_5fpred(s: &mut Store, v52: Term, v44: Term, v5: Term, v8: Term, v2: Term) -> CheckResult<Option<Term>> {
let v53 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v44, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24seq_5fempty(s, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v56, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24str_5freduction_5fpred(s, v8, v5, v2, v64, v63, v62, v55)
}
pub(super) fn more_25_eo__24str_5freduction_5fpred(s: &mut Store, v39: Term, v40: Term, v33: Term, v26: Term, v10: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v33, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v26, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v10, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v46, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v45, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24str_5freduction_5fpred(s, v52, v44, v5, v8, v2)
}
pub(super) fn more_24_eo__24str_5freduction_5fpred(s: &mut Store, v28: Term, v2: Term, v8: Term, v27: Term, v26: Term, v10: Term, v5: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v27, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v34, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24str_5freduction_5fpred(s, v39, v40, v33, v26, v10, v8, v5, v2)
}
pub(super) fn more_23_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v16: Term, v13: Term, v5: Term, v12: Term, v11: Term, v10: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v16, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v12, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v11, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24str_5freduction_5fpred(s, v28, v2, v8, v27, v26, v10, v5)
}
pub(super) fn case_2_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24str_5freduction_5fpred(s, v8, v2, v16, v13, v5, v12, v11, v10)
}
pub(super) fn more_80_eo__24str_5freduction_5fpred(s: &mut Store, v300: Term, v304: Term, v299: Term, v8: Term, v298: Term, v35: Term) -> CheckResult<Option<Term>> {
let v305 = match s.apply(v300, v304) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v299, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v306, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.apply(v298, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v35, v308) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v309))
}
pub(super) fn more_79_eo__24str_5freduction_5fpred(s: &mut Store, v243: Term, v292: Term, v242: Term, v138: Term, v40: Term, v8: Term, v5: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v293 = match s.apply(v243, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v293, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v242, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v138, v296) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v40, v297) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v301, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v302, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v303, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_80_eo__24str_5freduction_5fpred(s, v300, v304, v299, v8, v298, v35)
}
pub(super) fn more_78_eo__24str_5freduction_5fpred(s: &mut Store, v280: Term, v5: Term, v278: Term, v274: Term, v273: Term, v272: Term, v259: Term, v245: Term, v244: Term, v243: Term, v242: Term, v138: Term, v40: Term, v8: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v281 = match s.apply(v280, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v281, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.apply(v278, v283) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.apply(v274, v284) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match eo__24eo_5ftypeof(s, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match eo__24eo_5fnil(s, v273, v286) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.apply(v272, v287) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.apply(v259, v288) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v245, v289) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v290, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.apply(v244, v291) { Ok(v) => v, Err(e) => return Err(e) };
more_79_eo__24str_5freduction_5fpred(s, v243, v292, v242, v138, v40, v8, v5, v2, v35)
}
pub(super) fn more_77_eo__24str_5freduction_5fpred(s: &mut Store, v268: Term, v264: Term, v260: Term, v8: Term, v5: Term, v259: Term, v245: Term, v244: Term, v243: Term, v242: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v269 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v268, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v264, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v260, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v275, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v276, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v279, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_78_eo__24str_5freduction_5fpred(s, v280, v5, v278, v274, v273, v272, v259, v245, v244, v243, v242, v138, v40, v8, v2, v35)
}
pub(super) fn more_76_eo__24str_5freduction_5fpred(s: &mut Store, v251: Term, v256: Term, v247: Term, v246: Term, v5: Term, v8: Term, v245: Term, v244: Term, v243: Term, v242: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v257 = match s.apply(v251, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v247, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v246, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v261, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v262, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v266, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v265, v267) { Ok(v) => v, Err(e) => return Err(e) };
more_77_eo__24str_5freduction_5fpred(s, v268, v264, v260, v8, v5, v259, v245, v244, v243, v242, v138, v40, v2, v35)
}
pub(super) fn more_75_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v244: Term, v243: Term, v242: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v245 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v248, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v249, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v252, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v253, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v254, v255) { Ok(v) => v, Err(e) => return Err(e) };
more_76_eo__24str_5freduction_5fpred(s, v251, v256, v247, v246, v5, v8, v245, v244, v243, v242, v138, v40, v2, v35)
}
pub(super) fn more_74_eo__24str_5freduction_5fpred(s: &mut Store, v231: Term, v232: Term, v228: Term, v224: Term, v223: Term, v222: Term, v163: Term, v161: Term, v147: Term, v139: Term, v8: Term, v5: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v233 = match s.apply(v231, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v228, v233) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v224, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match eo__24eo_5ftypeof(s, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match eo__24eo_5fnil(s, v223, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v222, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v163, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v161, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v147, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v139, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_75_eo__24str_5freduction_5fpred(s, v8, v5, v244, v243, v242, v138, v40, v2, v35)
}
pub(super) fn more_73_eo__24str_5freduction_5fpred(s: &mut Store, v165: Term, v220: Term, v164: Term, v8: Term, v5: Term, v163: Term, v161: Term, v147: Term, v139: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v221 = match s.apply(v165, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v164, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v225, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v226, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v229, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v230, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_74_eo__24str_5freduction_5fpred(s, v231, v232, v228, v224, v223, v222, v163, v161, v147, v139, v8, v5, v138, v40, v2, v35)
}
pub(super) fn more_72_eo__24str_5freduction_5fpred(s: &mut Store, v198: Term, v208: Term, v197: Term, v196: Term, v5: Term, v195: Term, v191: Term, v165: Term, v164: Term, v8: Term, v163: Term, v161: Term, v147: Term, v139: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v209 = match s.apply(v198, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v197, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v196, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v213, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v212, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v215, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v211, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v195, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v191, v219) { Ok(v) => v, Err(e) => return Err(e) };
more_73_eo__24str_5freduction_5fpred(s, v165, v220, v164, v8, v5, v163, v161, v147, v139, v138, v40, v2, v35)
}
pub(super) fn more_71_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v196: Term, v195: Term, v191: Term, v165: Term, v164: Term, v163: Term, v161: Term, v147: Term, v139: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v197 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v199, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v200, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v203, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v205, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.apply(v202, v207) { Ok(v) => v, Err(e) => return Err(e) };
more_72_eo__24str_5freduction_5fpred(s, v198, v208, v197, v196, v5, v195, v191, v165, v164, v8, v163, v161, v147, v139, v138, v40, v2, v35)
}
pub(super) fn more_70_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v184: Term, v183: Term, v167: Term, v8: Term, v165: Term, v164: Term, v163: Term, v161: Term, v147: Term, v139: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v185 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v185, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v184, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v187, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v183, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v167, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v193, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v192, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_71_eo__24str_5freduction_5fpred(s, v8, v5, v196, v195, v191, v165, v164, v163, v161, v147, v139, v138, v40, v2, v35)
}
pub(super) fn more_69_eo__24str_5freduction_5fpred(s: &mut Store, v172: Term, v8: Term, v5: Term, v170: Term, v169: Term, v168: Term, v167: Term, v165: Term, v164: Term, v163: Term, v161: Term, v147: Term, v139: Term, v138: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v173 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v172, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v175, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v176, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v177, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v174, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v170, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v169, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v168, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_70_eo__24str_5freduction_5fpred(s, v5, v184, v183, v167, v8, v165, v164, v163, v161, v147, v139, v138, v40, v2, v35)
}
pub(super) fn more_68_eo__24str_5freduction_5fpred(s: &mut Store, v148: Term, v160: Term, v2: Term, v8: Term, v5: Term, v147: Term, v139: Term, v138: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v161 = match s.apply(v148, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v162, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v166, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_69_eo__24str_5freduction_5fpred(s, v172, v8, v5, v170, v169, v168, v167, v165, v164, v163, v161, v147, v139, v138, v40, v2, v35)
}
pub(super) fn more_67_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v148: Term, v2: Term, v147: Term, v139: Term, v138: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v149 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v150, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v151, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v154, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v156, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v153, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v149, v159) { Ok(v) => v, Err(e) => return Err(e) };
more_68_eo__24str_5freduction_5fpred(s, v148, v160, v2, v8, v5, v147, v139, v138, v40, v35)
}
pub(super) fn more_66_eo__24str_5freduction_5fpred(s: &mut Store, v43: Term, v136: Term, v41: Term, v8: Term, v5: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v137 = match s.apply(v43, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v41, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v142, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v144, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v141, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v140, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_67_eo__24str_5freduction_5fpred(s, v8, v5, v148, v2, v147, v139, v138, v40, v35)
}
pub(super) fn more_65_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v124: Term, v120: Term, v119: Term, v118: Term, v59: Term, v57: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v125 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v125, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v127, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v124, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v120, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match eo__24eo_5ftypeof(s, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match eo__24eo_5fnil(s, v119, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v118, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v59, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v57, v135) { Ok(v) => v, Err(e) => return Err(e) };
more_66_eo__24str_5freduction_5fpred(s, v43, v136, v41, v8, v5, v2, v40, v35)
}
pub(super) fn more_64_eo__24str_5freduction_5fpred(s: &mut Store, v111: Term, v112: Term, v107: Term, v91: Term, v87: Term, v61: Term, v60: Term, v8: Term, v5: Term, v59: Term, v57: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v111, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v107, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v91, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v87, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v61, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v60, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v121, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v122, v123) { Ok(v) => v, Err(e) => return Err(e) };
more_65_eo__24str_5freduction_5fpred(s, v8, v5, v124, v120, v119, v118, v59, v57, v43, v41, v2, v40, v35)
}
pub(super) fn more_63_eo__24str_5freduction_5fpred(s: &mut Store, v100: Term, v5: Term, v98: Term, v94: Term, v93: Term, v92: Term, v91: Term, v87: Term, v61: Term, v60: Term, v8: Term, v59: Term, v57: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v101 = match s.apply(v100, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v101, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v98, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v94, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v93, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v92, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v108, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_64_eo__24str_5freduction_5fpred(s, v111, v112, v107, v91, v87, v61, v60, v8, v5, v59, v57, v43, v41, v2, v40, v35)
}
pub(super) fn more_62_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v88: Term, v5: Term, v87: Term, v61: Term, v60: Term, v59: Term, v57: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v89 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v88, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_63_eo__24str_5freduction_5fpred(s, v100, v5, v98, v94, v93, v92, v91, v87, v61, v60, v8, v59, v57, v43, v41, v2, v40, v35)
}
pub(super) fn more_61_eo__24str_5freduction_5fpred(s: &mut Store, v66: Term, v76: Term, v65: Term, v64: Term, v5: Term, v63: Term, v8: Term, v61: Term, v60: Term, v59: Term, v57: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v66, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v65, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v64, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v83, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v79, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v63, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_62_eo__24str_5freduction_5fpred(s, v8, v88, v5, v87, v61, v60, v59, v57, v43, v41, v2, v40, v35)
}
pub(super) fn more_60_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v64: Term, v63: Term, v61: Term, v60: Term, v59: Term, v57: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v65 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v68, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v72, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v70, v75) { Ok(v) => v, Err(e) => return Err(e) };
more_61_eo__24str_5freduction_5fpred(s, v66, v76, v65, v64, v5, v63, v8, v61, v60, v59, v57, v43, v41, v2, v40, v35)
}
pub(super) fn more_59_eo__24str_5freduction_5fpred(s: &mut Store, v52: Term, v49: Term, v45: Term, v44: Term, v5: Term, v8: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v53 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v49, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v45, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v44, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_60_eo__24str_5freduction_5fpred(s, v8, v5, v64, v63, v61, v60, v59, v57, v43, v41, v2, v40, v35)
}
pub(super) fn more_58_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v41 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_59_eo__24str_5freduction_5fpred(s, v52, v49, v45, v44, v5, v8, v43, v41, v2, v40, v35)
}
pub(super) fn more_57_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v28: Term, v26: Term, v24: Term, v16: Term, v8: Term, v5: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fnil(s, v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v26, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v24, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v16, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_58_eo__24str_5freduction_5fpred(s, v8, v5, v2, v40, v35)
}
pub(super) fn more_56_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_57_eo__24str_5freduction_5fpred(s, v2, v28, v26, v24, v16, v8, v5)
}
pub(super) fn case_3_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24seq_5fempty(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_56_eo__24str_5freduction_5fpred(s, v8, v5, v2, v16)
}
pub(super) fn cases_0_0_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_102_eo__24str_5freduction_5fpred(s: &mut Store, v260: Term, v264: Term, v259: Term) -> CheckResult<Option<Term>> {
let v265 = match s.apply(v260, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v265, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v259, v267) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v268))
}
pub(super) fn more_101_eo__24str_5freduction_5fpred(s: &mut Store, v46: Term, v252: Term, v45: Term, v35: Term, v21: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v253 = match s.apply(v46, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v253, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v45, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v35, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v21, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v9, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v262, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v261, v263) { Ok(v) => v, Err(e) => return Err(e) };
more_102_eo__24str_5freduction_5fpred(s, v260, v264, v259)
}
pub(super) fn more_100_eo__24str_5freduction_5fpred(s: &mut Store, v226: Term, v240: Term, v224: Term, v223: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v241 = match s.apply(v226, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v224, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v242, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.apply(v223, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v141, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v83, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v247, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v82, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v66, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v55, v251) { Ok(v) => v, Err(e) => return Err(e) };
more_101_eo__24str_5freduction_5fpred(s, v46, v252, v45, v35, v21, v9, v2)
}
pub(super) fn more_99_eo__24str_5freduction_5fpred(s: &mut Store, v228: Term, v226: Term, v224: Term, v223: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v229 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo__24emb_5fVar, &[v230, v231]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v229, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v234, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v236, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v233, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v228, v239) { Ok(v) => v, Err(e) => return Err(e) };
more_100_eo__24str_5freduction_5fpred(s, v226, v240, v224, v223, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9, v2)
}
pub(super) fn more_98_eo__24str_5freduction_5fpred(s: &mut Store, v216: Term, v196: Term, v195: Term, v142: Term, v2: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v217 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v216, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v196, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v219, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v195, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v142, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v225, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v227, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_99_eo__24str_5freduction_5fpred(s, v228, v226, v224, v223, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9, v2)
}
pub(super) fn more_97_eo__24str_5freduction_5fpred(s: &mut Store, v200: Term, v204: Term, v199: Term, v198: Term, v197: Term, v196: Term, v195: Term, v142: Term, v2: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v205 = match s.apply(v200, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo__24emb_5fVar, &[v206, v207]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v205, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v209, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v199, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v198, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v213, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v197, v215) { Ok(v) => v, Err(e) => return Err(e) };
more_98_eo__24str_5freduction_5fpred(s, v216, v196, v195, v142, v2, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_96_eo__24str_5freduction_5fpred(s: &mut Store, v191: Term, v192: Term, v163: Term, v143: Term, v2: Term, v142: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v193 = match s.apply(v191, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v163, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v143, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v202, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v201, v203) { Ok(v) => v, Err(e) => return Err(e) };
more_97_eo__24str_5freduction_5fpred(s, v200, v204, v199, v198, v197, v196, v195, v142, v2, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_95_eo__24str_5freduction_5fpred(s: &mut Store, v176: Term, v180: Term, v175: Term, v174: Term, v173: Term, v164: Term, v163: Term, v143: Term, v2: Term, v142: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v181 = match s.apply(v176, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v175, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v182, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v174, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v185, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v173, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v164, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v189, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_96_eo__24str_5freduction_5fpred(s, v191, v192, v163, v143, v2, v142, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_94_eo__24str_5freduction_5fpred(s: &mut Store, v167: Term, v168: Term, v166: Term, v165: Term, v2: Term, v164: Term, v163: Term, v143: Term, v142: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v169 = match s.construct(Constructor::eo__24emb_5fVar, &[v167, v168]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v166, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v170, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v165, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v178, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v177, v179) { Ok(v) => v, Err(e) => return Err(e) };
more_95_eo__24str_5freduction_5fpred(s, v176, v180, v175, v174, v173, v164, v163, v143, v2, v142, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_93_eo__24str_5freduction_5fpred(s: &mut Store, v156: Term, v146: Term, v145: Term, v144: Term, v2: Term, v143: Term, v142: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v157 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v156, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v146, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v145, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v160, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v144, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_94_eo__24str_5freduction_5fpred(s, v167, v168, v166, v165, v2, v164, v163, v143, v142, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_92_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v144: Term, v143: Term, v142: Term, v141: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v145 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v148, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v147, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo__24emb_5fVar, &[v153, v154]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v152, v155) { Ok(v) => v, Err(e) => return Err(e) };
more_93_eo__24str_5freduction_5fpred(s, v156, v146, v145, v144, v2, v143, v142, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_91_eo__24str_5freduction_5fpred(s: &mut Store, v132: Term, v124: Term, v121: Term, v120: Term, v100: Term, v84: Term, v2: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v133 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v132, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v124, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v121, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v136, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v120, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v100, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v84, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_92_eo__24str_5freduction_5fpred(s, v2, v144, v143, v142, v141, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_90_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v120: Term, v100: Term, v84: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v121 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v122, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo__24emb_5fVar, &[v128, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v127, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v125, v131) { Ok(v) => v, Err(e) => return Err(e) };
more_91_eo__24str_5freduction_5fpred(s, v132, v124, v121, v120, v100, v84, v2, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_89_eo__24str_5freduction_5fpred(s: &mut Store, v104: Term, v108: Term, v103: Term, v102: Term, v101: Term, v2: Term, v100: Term, v84: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v109 = match s.apply(v104, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo__24emb_5fVar, &[v110, v111]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v109, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v103, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v102, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v117, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v101, v119) { Ok(v) => v, Err(e) => return Err(e) };
more_90_eo__24str_5freduction_5fpred(s, v2, v120, v100, v84, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_88_eo__24str_5freduction_5fpred(s: &mut Store, v95: Term, v96: Term, v92: Term, v87: Term, v85: Term, v2: Term, v84: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v97 = match s.apply(v95, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v92, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v87, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v85, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v105, v107) { Ok(v) => v, Err(e) => return Err(e) };
more_89_eo__24str_5freduction_5fpred(s, v104, v108, v103, v102, v101, v2, v100, v84, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_87_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v84: Term, v83: Term, v82: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v85 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v86, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__24emb_5fVar, &[v89, v90]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v88, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v93, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_88_eo__24str_5freduction_5fpred(s, v95, v96, v92, v87, v85, v2, v84, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_86_eo__24str_5freduction_5fpred(s: &mut Store, v69: Term, v72: Term, v2: Term, v68: Term, v67: Term, v66: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v73 = match s.apply(v69, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v73, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v68, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v67, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_87_eo__24str_5freduction_5fpred(s, v2, v84, v83, v82, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_85_eo__24str_5freduction_5fpred(s: &mut Store, v59: Term, v60: Term, v58: Term, v57: Term, v56: Term, v2: Term, v55: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v61 = match s.construct(Constructor::eo__24emb_5fVar, &[v59, v60]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v58, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v57, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v56, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo__24emb_5fVar, &[v70, v71]) { Ok(v) => v, Err(e) => return Err(e) };
more_86_eo__24str_5freduction_5fpred(s, v69, v72, v2, v68, v67, v66, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_84_eo__24str_5freduction_5fpred(s: &mut Store, v48: Term, v47: Term, v2: Term, v46: Term, v45: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v49 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo__24emb_5fVar, &[v49, v50]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v48, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v47, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_85_eo__24str_5freduction_5fpred(s, v59, v60, v58, v57, v56, v2, v55, v46, v45, v35, v21, v9)
}
pub(super) fn more_83_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v36: Term, v35: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v37 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v37, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v39, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v36, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_84_eo__24str_5freduction_5fpred(s, v48, v47, v2, v46, v45, v35, v21, v9)
}
pub(super) fn more_82_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v24: Term, v22: Term, v21: Term, v9: Term) -> CheckResult<Option<Term>> {
let v25 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v27, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v26, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v24, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v22, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_83_eo__24str_5freduction_5fpred(s, v2, v36, v35, v21, v9)
}
pub(super) fn more_81_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v12: Term, v11: Term, v10: Term, v9: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v10, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_82_eo__24str_5freduction_5fpred(s, v2, v24, v22, v21, v9)
}
pub(super) fn case_4_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v4, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_81_eo__24str_5freduction_5fpred(s, v2, v12, v11, v10, v9)
}
pub(super) fn more_127_eo__24str_5freduction_5fpred(s: &mut Store, v157: Term, v300: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v301 = match s.apply(v157, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v146, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v137, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.apply(v303, v304) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v136, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v128, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.apply(v118, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v104, v308) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v309))
}
pub(super) fn more_126_eo__24str_5freduction_5fpred(s: &mut Store, v283: Term, v288: Term, v278: Term, v276: Term, v270: Term, v269: Term, v224: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v289 = match s.apply(v283, v288) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v278, v289) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v276, v290) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.apply(v270, v291) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v292, v293) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v269, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v224, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v170, v296) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.apply(v297, v298) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v169, v299) { Ok(v) => v, Err(e) => return Err(e) };
more_127_eo__24str_5freduction_5fpred(s, v157, v300, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_125_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v276: Term, v270: Term, v269: Term, v224: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v277 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v277, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo__24emb_5fVar, &[v280, v281]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v279, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v284, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.apply(v286, v287) { Ok(v) => v, Err(e) => return Err(e) };
more_126_eo__24str_5freduction_5fpred(s, v283, v288, v278, v276, v270, v269, v224, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_124_eo__24str_5freduction_5fpred(s: &mut Store, v246: Term, v264: Term, v245: Term, v225: Term, v2: Term, v224: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v265 = match s.apply(v246, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v265, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v245, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v225, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v273, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v272, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v271, v275) { Ok(v) => v, Err(e) => return Err(e) };
more_125_eo__24str_5freduction_5fpred(s, v2, v276, v270, v269, v224, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_123_eo__24str_5freduction_5fpred(s: &mut Store, v252: Term, v251: Term, v249: Term, v248: Term, v247: Term, v246: Term, v245: Term, v225: Term, v2: Term, v224: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v253 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo__24emb_5fVar, &[v252, v253]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v251, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v255, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v249, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v248, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v259, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v247, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v262, v263) { Ok(v) => v, Err(e) => return Err(e) };
more_124_eo__24str_5freduction_5fpred(s, v246, v264, v245, v225, v2, v224, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_122_eo__24str_5freduction_5fpred(s: &mut Store, v239: Term, v240: Term, v227: Term, v226: Term, v2: Term, v225: Term, v224: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v241 = match s.apply(v239, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v227, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v242, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.apply(v226, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v250, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_123_eo__24str_5freduction_5fpred(s, v252, v251, v249, v248, v247, v246, v245, v225, v2, v224, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_121_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v228: Term, v227: Term, v226: Term, v225: Term, v224: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v229 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v230, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo__24emb_5fVar, &[v232, v233]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v231, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v235, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v229, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v228, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_122_eo__24str_5freduction_5fpred(s, v239, v240, v227, v226, v2, v225, v224, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_120_eo__24str_5freduction_5fpred(s: &mut Store, v215: Term, v216: Term, v207: Term, v204: Term, v203: Term, v187: Term, v171: Term, v2: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v217 = match s.apply(v215, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v207, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v204, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v219, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v203, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v187, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v171, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_121_eo__24str_5freduction_5fpred(s, v2, v228, v227, v226, v225, v224, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_119_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v204: Term, v203: Term, v187: Term, v171: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v205 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v205, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v209, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo__24emb_5fVar, &[v211, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v210, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v208, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_120_eo__24str_5freduction_5fpred(s, v215, v216, v207, v204, v203, v187, v171, v2, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_118_eo__24str_5freduction_5fpred(s: &mut Store, v192: Term, v190: Term, v189: Term, v188: Term, v2: Term, v187: Term, v171: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v193 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo__24emb_5fVar, &[v193, v194]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v192, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v196, v197) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v190, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v189, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v200, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v188, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_119_eo__24str_5freduction_5fpred(s, v2, v204, v203, v187, v171, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_117_eo__24str_5freduction_5fpred(s: &mut Store, v180: Term, v179: Term, v174: Term, v172: Term, v2: Term, v171: Term, v170: Term, v169: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v181 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v180, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v182, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v179, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v174, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v172, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v191, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_118_eo__24str_5freduction_5fpred(s, v192, v190, v189, v188, v2, v187, v171, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_116_eo__24str_5freduction_5fpred(s: &mut Store, v158: Term, v168: Term, v2: Term, v157: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v169 = match s.apply(v158, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v173, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo__24emb_5fVar, &[v176, v177]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v175, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_117_eo__24str_5freduction_5fpred(s, v180, v179, v174, v172, v2, v171, v170, v169, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_115_eo__24str_5freduction_5fpred(s: &mut Store, v147: Term, v156: Term, v2: Term, v146: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v157 = match s.apply(v147, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo__24emb_5fVar, &[v161, v162]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v160, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v165, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v164, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v159, v167) { Ok(v) => v, Err(e) => return Err(e) };
more_116_eo__24str_5freduction_5fpred(s, v158, v168, v2, v157, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_114_eo__24str_5freduction_5fpred(s: &mut Store, v143: Term, v144: Term, v138: Term, v2: Term, v137: Term, v136: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v145 = match s.apply(v143, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v138, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo__24emb_5fVar, &[v150, v151]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v149, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v153, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v148, v155) { Ok(v) => v, Err(e) => return Err(e) };
more_115_eo__24str_5freduction_5fpred(s, v147, v156, v2, v146, v137, v136, v128, v118, v104)
}
pub(super) fn more_113_eo__24str_5freduction_5fpred(s: &mut Store, v130: Term, v132: Term, v129: Term, v2: Term, v128: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v133 = match s.apply(v130, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v133, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v129, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo__24emb_5fVar, &[v140, v141]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v139, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_114_eo__24str_5freduction_5fpred(s, v143, v144, v138, v2, v137, v136, v128, v118, v104)
}
pub(super) fn more_112_eo__24str_5freduction_5fpred(s: &mut Store, v120: Term, v2: Term, v119: Term, v118: Term, v104: Term) -> CheckResult<Option<Term>> {
let v121 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v120, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v124, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v122, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v119, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v131, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_113_eo__24str_5freduction_5fpred(s, v130, v132, v129, v2, v128, v118, v104)
}
pub(super) fn more_111_eo__24str_5freduction_5fpred(s: &mut Store, v108: Term, v2: Term, v107: Term, v106: Term, v105: Term, v104: Term) -> CheckResult<Option<Term>> {
let v109 = match s.apply(v108, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v106, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v112, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v114, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v113, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v111, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v105, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_112_eo__24str_5freduction_5fpred(s, v120, v2, v119, v118, v104)
}
pub(super) fn more_110_eo__24str_5freduction_5fpred(s: &mut Store, v96: Term, v30: Term, v24: Term, v23: Term, v13: Term, v2: Term) -> CheckResult<Option<Term>> {
let v97 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v30, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v24, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v100, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v23, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v13, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_111_eo__24str_5freduction_5fpred(s, v108, v2, v107, v106, v105, v104)
}
pub(super) fn more_109_eo__24str_5freduction_5fpred(s: &mut Store, v84: Term, v69: Term, v68: Term, v49: Term, v48: Term, v39: Term, v31: Term, v30: Term, v24: Term, v23: Term, v13: Term, v2: Term) -> CheckResult<Option<Term>> {
let v85 = match s.literal(Lit::Numeral(Integer::from(10u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v84, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v69, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v87, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v68, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v49, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v91, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v48, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v39, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v31, v95) { Ok(v) => v, Err(e) => return Err(e) };
more_110_eo__24str_5freduction_5fpred(s, v96, v30, v24, v23, v13, v2)
}
pub(super) fn more_108_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v72: Term, v71: Term, v70: Term, v69: Term, v68: Term, v49: Term, v48: Term, v39: Term, v31: Term, v30: Term, v24: Term, v23: Term, v13: Term) -> CheckResult<Option<Term>> {
let v73 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v74, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v77, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v72, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v71, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v81, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v70, v83) { Ok(v) => v, Err(e) => return Err(e) };
more_109_eo__24str_5freduction_5fpred(s, v84, v69, v68, v49, v48, v39, v31, v30, v24, v23, v13, v2)
}
pub(super) fn more_107_eo__24str_5freduction_5fpred(s: &mut Store, v53: Term, v60: Term, v52: Term, v51: Term, v50: Term, v2: Term, v49: Term, v48: Term, v39: Term, v31: Term, v30: Term, v24: Term, v23: Term, v13: Term) -> CheckResult<Option<Term>> {
let v61 = match s.apply(v53, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v52, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(Integer::from(48u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v51, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v65, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v50, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_108_eo__24str_5freduction_5fpred(s, v2, v72, v71, v70, v69, v68, v49, v48, v39, v31, v30, v24, v23, v13)
}
pub(super) fn more_106_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v48: Term, v39: Term, v31: Term, v30: Term, v24: Term, v23: Term, v13: Term) -> CheckResult<Option<Term>> {
let v49 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v58, v59) { Ok(v) => v, Err(e) => return Err(e) };
more_107_eo__24str_5freduction_5fpred(s, v53, v60, v52, v51, v50, v2, v49, v48, v39, v31, v30, v24, v23, v13)
}
pub(super) fn more_105_eo__24str_5freduction_5fpred(s: &mut Store, v36: Term, v32: Term, v2: Term, v31: Term, v30: Term, v24: Term, v23: Term, v13: Term) -> CheckResult<Option<Term>> {
let v37 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v32, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v40, v47) { Ok(v) => v, Err(e) => return Err(e) };
more_106_eo__24str_5freduction_5fpred(s, v2, v48, v39, v31, v30, v24, v23, v13)
}
pub(super) fn more_104_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v24: Term, v23: Term, v13: Term) -> CheckResult<Option<Term>> {
let v25 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
more_105_eo__24str_5freduction_5fpred(s, v36, v32, v2, v31, v30, v24, v23, v13)
}
pub(super) fn more_103_eo__24str_5freduction_5fpred(s: &mut Store, v4: Term, v12: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v4, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_104_eo__24str_5freduction_5fpred(s, v2, v24, v23, v13)
}
pub(super) fn case_5_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_103_eo__24str_5freduction_5fpred(s, v4, v12, v2)
}
pub(super) fn more_139_eo__24str_5freduction_5fpred(s: &mut Store, v141: Term, v146: Term, v139: Term, v135: Term, v104: Term, v103: Term, v89: Term, v24: Term) -> CheckResult<Option<Term>> {
let v147 = match s.apply(v141, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v139, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v135, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v104, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v150, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v103, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v89, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v24, v154) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v155))
}
pub(super) fn more_138_eo__24str_5freduction_5fpred(s: &mut Store, v105: Term, v134: Term, v5: Term, v2: Term, v104: Term, v103: Term, v89: Term, v24: Term) -> CheckResult<Option<Term>> {
let v135 = match s.apply(v105, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v136, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v140, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v142, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v144, v145) { Ok(v) => v, Err(e) => return Err(e) };
more_139_eo__24str_5freduction_5fpred(s, v141, v146, v139, v135, v104, v103, v89, v24)
}
pub(super) fn more_137_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v122: Term, v118: Term, v107: Term, v106: Term, v105: Term, v5: Term, v104: Term, v103: Term, v89: Term, v24: Term) -> CheckResult<Option<Term>> {
let v123 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v125, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v127, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v124, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v122, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v118, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v107, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v106, v133) { Ok(v) => v, Err(e) => return Err(e) };
more_138_eo__24str_5freduction_5fpred(s, v105, v134, v5, v2, v104, v103, v89, v24)
}
pub(super) fn more_136_eo__24str_5freduction_5fpred(s: &mut Store, v110: Term, v2: Term, v109: Term, v5: Term, v107: Term, v106: Term, v105: Term, v104: Term, v103: Term, v89: Term, v24: Term) -> CheckResult<Option<Term>> {
let v111 = match s.apply(v110, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v114, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v111, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v109, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v119, v121) { Ok(v) => v, Err(e) => return Err(e) };
more_137_eo__24str_5freduction_5fpred(s, v2, v122, v118, v107, v106, v105, v5, v104, v103, v89, v24)
}
pub(super) fn more_135_eo__24str_5freduction_5fpred(s: &mut Store, v93: Term, v98: Term, v92: Term, v91: Term, v2: Term, v90: Term, v5: Term, v89: Term, v24: Term) -> CheckResult<Option<Term>> {
let v99 = match s.apply(v93, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v92, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v91, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v90, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_136_eo__24str_5freduction_5fpred(s, v110, v2, v109, v5, v107, v106, v105, v104, v103, v89, v24)
}
pub(super) fn more_134_eo__24str_5freduction_5fpred(s: &mut Store, v36: Term, v86: Term, v27: Term, v25: Term, v5: Term, v2: Term, v24: Term) -> CheckResult<Option<Term>> {
let v87 = match s.apply(v36, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v27, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v25, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v95, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_135_eo__24str_5freduction_5fpred(s, v93, v98, v92, v91, v2, v90, v5, v89, v24)
}
pub(super) fn more_133_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v74: Term, v45: Term, v36: Term, v27: Term, v25: Term, v24: Term) -> CheckResult<Option<Term>> {
let v75 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v78, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v76, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match eo__24eo_5ftypeof(s, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match eo__24eo_5fnil(s, v75, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v74, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v45, v85) { Ok(v) => v, Err(e) => return Err(e) };
more_134_eo__24str_5freduction_5fpred(s, v36, v86, v27, v25, v5, v2, v24)
}
pub(super) fn more_132_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v62: Term, v58: Term, v47: Term, v46: Term, v5: Term, v45: Term, v36: Term, v27: Term, v25: Term, v24: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v65, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v64, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v62, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v58, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v47, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v46, v73) { Ok(v) => v, Err(e) => return Err(e) };
more_133_eo__24str_5freduction_5fpred(s, v5, v2, v74, v45, v36, v27, v25, v24)
}
pub(super) fn more_131_eo__24str_5freduction_5fpred(s: &mut Store, v50: Term, v2: Term, v49: Term, v5: Term, v47: Term, v46: Term, v45: Term, v36: Term, v27: Term, v25: Term, v24: Term) -> CheckResult<Option<Term>> {
let v51 = match s.apply(v50, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v54, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v51, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v49, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
more_132_eo__24str_5freduction_5fpred(s, v2, v62, v58, v47, v46, v5, v45, v36, v27, v25, v24)
}
pub(super) fn more_130_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v38: Term, v37: Term, v36: Term, v27: Term, v25: Term, v24: Term) -> CheckResult<Option<Term>> {
let v39 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v39, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v38, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v37, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_131_eo__24str_5freduction_5fpred(s, v50, v2, v49, v5, v47, v46, v45, v36, v27, v25, v24)
}
pub(super) fn more_129_eo__24str_5freduction_5fpred(s: &mut Store, v26: Term, v5: Term, v2: Term, v25: Term, v24: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v26, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v29, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_130_eo__24str_5freduction_5fpred(s, v5, v2, v38, v37, v36, v27, v25, v24)
}
pub(super) fn more_128_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v14: Term, v13: Term, v7: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v14, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v7, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_129_eo__24str_5freduction_5fpred(s, v26, v5, v2, v25, v24)
}
pub(super) fn case_6_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_128_eo__24str_5freduction_5fpred(s, v5, v2, v14, v13, v7)
}
pub(super) fn if_140_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v50 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v51, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v54, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v53, v58) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v59)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_141_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v73 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v74, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v78, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v77, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v76, v81) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v82)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_142_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v101 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v102, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v105, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v104, v109) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v110)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_143_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v157 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v157, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v158, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v162, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v161, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v164, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v160, v165) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v166)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_144_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v183 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v184, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v188, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v187, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v190, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v186, v191) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v192)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_145_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v211 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v211, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v212, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v216, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v215, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v218, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v214, v219) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v220)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_146_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v266 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v266, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v267, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v271, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v270, v272) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v273, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v269, v274) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v275)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_147_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v288 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.apply(v288, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v289, v290) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v293, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v292, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v295, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v291, v296) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v297)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_166_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v312: Term, v311: Term, v310: Term) -> CheckResult<Option<Term>> {
let v313 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v313, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v314, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v315, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.apply(v312, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v311, v317) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v318, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.apply(v310, v319) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v320))
}
pub(super) fn more_165_eo__24str_5freduction_5fpred(s: &mut Store, v280: Term, v300: Term, v279: Term, v278: Term, v260: Term, v259: Term, v245: Term, v135: Term, v27: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v301 = match s.apply(v280, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v279, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v278, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v260, v303) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v304, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v259, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.apply(v245, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v135, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v27, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_166_eo__24str_5freduction_5fpred(s, v8, v5, v2, v312, v311, v310)
}
pub(super) fn case_0_eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_0_eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_0_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
Ok(Some(Next::Again([v2])))
}
pub(super) fn case_1_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_2_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24is_5fseq_5fconst_5frec(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24is_5fseq_5fconst_5frec(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
// EO program "$is_seq_const_rec"
pub fn eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(914), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fseq_5fconst_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(914), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5fseq_5fconst(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fseq_5fconst(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_seq_const"
pub fn eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5fseq_5fconst(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24str_5fvalue_5flen(s: &mut Store, v2: Term, v3: Term, a0: Term) -> CheckResult<Term> {
if v2 != v3 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListLength, &[v4, a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
pub(super) fn if_1_eo__24str_5fvalue_5flen(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.builtin_core(EvalOp::Length, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match eo__24is_5fseq_5fconst(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match requires_0_eo__24str_5fvalue_5flen(s, v2, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::IsStr, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_1_eo__24str_5fvalue_5flen(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fvalue_5flen(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fvalue_5flen(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_value_len"
pub fn eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fvalue_5flen(s, a0);
s.leave();
result
}
pub(super) fn more_164_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v278: Term, v260: Term, v259: Term, v245: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v279 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v281, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v282, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.builtin_core(EvalOp::IsEq, &[v285, v286]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match if_147_eo__24str_5freduction_5fpred(s, v287, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.apply(v284, v298) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v283, v299) { Ok(v) => v, Err(e) => return Err(e) };
more_165_eo__24str_5freduction_5fpred(s, v280, v300, v279, v278, v260, v259, v245, v135, v27, v8, v5, v2)
}
pub(super) fn more_163_eo__24str_5freduction_5fpred(s: &mut Store, v247: Term, v256: Term, v5: Term, v246: Term, v2: Term, v8: Term, v245: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v257 = match s.apply(v247, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v257, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v246, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.builtin_core(EvalOp::IsEq, &[v263, v264]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match if_146_eo__24str_5freduction_5fpred(s, v265, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v262, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v261, v277) { Ok(v) => v, Err(e) => return Err(e) };
more_164_eo__24str_5freduction_5fpred(s, v8, v5, v2, v278, v260, v259, v245, v135, v27)
}
pub(super) fn more_162_eo__24str_5freduction_5fpred(s: &mut Store, v136: Term, v244: Term, v8: Term, v5: Term, v2: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v245 = match s.apply(v136, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v250, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v251, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v253, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v249, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v248, v255) { Ok(v) => v, Err(e) => return Err(e) };
more_163_eo__24str_5freduction_5fpred(s, v247, v256, v5, v246, v2, v8, v245, v135, v27)
}
pub(super) fn more_161_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v232: Term, v231: Term, v230: Term, v171: Term, v147: Term, v138: Term, v136: Term, v2: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v233 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v233, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v234, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v236, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v232, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match eo__24eo_5ftypeof(s, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match eo__24eo_5fnil(s, v231, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v230, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v171, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v147, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v138, v243) { Ok(v) => v, Err(e) => return Err(e) };
more_162_eo__24str_5freduction_5fpred(s, v136, v244, v8, v5, v2, v135, v27)
}
pub(super) fn more_160_eo__24str_5freduction_5fpred(s: &mut Store, v210: Term, v2: Term, v8: Term, v5: Term, v207: Term, v206: Term, v205: Term, v203: Term, v199: Term, v173: Term, v172: Term, v171: Term, v147: Term, v138: Term, v136: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v221 = match if_145_eo__24str_5freduction_5fpred(s, v210, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v207, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v206, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v223, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v205, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.apply(v203, v226) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v199, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v173, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v172, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_161_eo__24str_5freduction_5fpred(s, v8, v5, v232, v231, v230, v171, v147, v138, v136, v2, v135, v27)
}
pub(super) fn more_159_eo__24str_5freduction_5fpred(s: &mut Store, v175: Term, v198: Term, v8: Term, v5: Term, v2: Term, v173: Term, v172: Term, v171: Term, v147: Term, v138: Term, v136: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v199 = match s.apply(v175, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v201, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v200, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_core(EvalOp::IsEq, &[v208, v209]) { Ok(v) => v, Err(e) => return Err(e) };
more_160_eo__24str_5freduction_5fpred(s, v210, v2, v8, v5, v207, v206, v205, v203, v199, v173, v172, v171, v147, v138, v136, v135, v27)
}
pub(super) fn more_158_eo__24str_5freduction_5fpred(s: &mut Store, v176: Term, v5: Term, v2: Term, v8: Term, v175: Term, v173: Term, v172: Term, v171: Term, v147: Term, v138: Term, v136: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v177 = match s.apply(v176, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.builtin_core(EvalOp::IsEq, &[v180, v181]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match if_144_eo__24str_5freduction_5fpred(s, v182, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v179, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v178, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.apply(v195, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v177, v197) { Ok(v) => v, Err(e) => return Err(e) };
more_159_eo__24str_5freduction_5fpred(s, v175, v198, v8, v5, v2, v173, v172, v171, v147, v138, v136, v135, v27)
}
pub(super) fn more_157_eo__24str_5freduction_5fpred(s: &mut Store, v154: Term, v2: Term, v8: Term, v5: Term, v153: Term, v152: Term, v149: Term, v148: Term, v147: Term, v138: Term, v136: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v155 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.builtin_core(EvalOp::IsEq, &[v154, v155]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match if_143_eo__24str_5freduction_5fpred(s, v156, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v153, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v152, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v149, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v148, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v174, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_158_eo__24str_5freduction_5fpred(s, v176, v5, v2, v8, v175, v173, v172, v171, v147, v138, v136, v135, v27)
}
pub(super) fn more_156_eo__24str_5freduction_5fpred(s: &mut Store, v142: Term, v5: Term, v140: Term, v139: Term, v8: Term, v2: Term, v138: Term, v136: Term, v135: Term, v27: Term) -> CheckResult<Option<Term>> {
let v143 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v142, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v144, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v140, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v139, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v150, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v151, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_157_eo__24str_5freduction_5fpred(s, v154, v2, v8, v5, v153, v152, v149, v148, v147, v138, v136, v135, v27)
}
pub(super) fn more_155_eo__24str_5freduction_5fpred(s: &mut Store, v120: Term, v130: Term, v61: Term, v45: Term, v36: Term, v28: Term, v8: Term, v5: Term, v2: Term, v27: Term) -> CheckResult<Option<Term>> {
let v131 = match s.apply(v120, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v61, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v45, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v36, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v28, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_156_eo__24str_5freduction_5fpred(s, v142, v5, v140, v139, v8, v2, v138, v136, v135, v27)
}
pub(super) fn more_154_eo__24str_5freduction_5fpred(s: &mut Store, v63: Term, v118: Term, v62: Term, v8: Term, v5: Term, v61: Term, v45: Term, v36: Term, v28: Term, v2: Term, v27: Term) -> CheckResult<Option<Term>> {
let v119 = match s.apply(v63, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v62, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v124, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v122, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match eo__24eo_5ftypeof(s, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match eo__24eo_5fnil(s, v121, v129) { Ok(v) => v, Err(e) => return Err(e) };
more_155_eo__24str_5freduction_5fpred(s, v120, v130, v61, v45, v36, v28, v8, v5, v2, v27)
}
pub(super) fn more_153_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v8: Term, v5: Term, v96: Term, v95: Term, v93: Term, v89: Term, v63: Term, v62: Term, v61: Term, v45: Term, v36: Term, v28: Term, v27: Term) -> CheckResult<Option<Term>> {
let v97 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.builtin_core(EvalOp::IsEq, &[v98, v99]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match if_142_eo__24str_5freduction_5fpred(s, v100, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v97, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v96, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v95, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v93, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v89, v117) { Ok(v) => v, Err(e) => return Err(e) };
more_154_eo__24str_5freduction_5fpred(s, v63, v118, v62, v8, v5, v61, v45, v36, v28, v2, v27)
}
pub(super) fn more_152_eo__24str_5freduction_5fpred(s: &mut Store, v68: Term, v84: Term, v67: Term, v65: Term, v8: Term, v5: Term, v2: Term, v63: Term, v62: Term, v61: Term, v45: Term, v36: Term, v28: Term, v27: Term) -> CheckResult<Option<Term>> {
let v85 = match s.apply(v68, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v85, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v67, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v65, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v90, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_153_eo__24str_5freduction_5fpred(s, v2, v8, v5, v96, v95, v93, v89, v63, v62, v61, v45, v36, v28, v27)
}
pub(super) fn more_151_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v62: Term, v61: Term, v45: Term, v36: Term, v28: Term, v27: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.builtin_core(EvalOp::IsEq, &[v70, v71]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match if_141_eo__24str_5freduction_5fpred(s, v72, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v69, v83) { Ok(v) => v, Err(e) => return Err(e) };
more_152_eo__24str_5freduction_5fpred(s, v68, v84, v67, v65, v8, v5, v2, v63, v62, v61, v45, v36, v28, v27)
}
pub(super) fn more_150_eo__24str_5freduction_5fpred(s: &mut Store, v40: Term, v5: Term, v38: Term, v37: Term, v2: Term, v8: Term, v36: Term, v28: Term, v27: Term) -> CheckResult<Option<Term>> {
let v41 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v38, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v37, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::IsEq, &[v47, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match if_140_eo__24str_5freduction_5fpred(s, v49, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v46, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_151_eo__24str_5freduction_5fpred(s, v8, v5, v2, v62, v61, v45, v36, v28, v27)
}
pub(super) fn more_149_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v28: Term, v27: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v30, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_150_eo__24str_5freduction_5fpred(s, v40, v5, v38, v37, v2, v8, v36, v28, v27)
}
pub(super) fn more_148_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v16: Term, v10: Term, v2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v17, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v10, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_149_eo__24str_5freduction_5fpred(s, v8, v5, v2, v28, v27)
}
pub(super) fn case_7_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_148_eo__24str_5freduction_5fpred(s, v8, v5, v16, v10, v2)
}
pub(super) fn cases_0_1_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_192_eo__24str_5freduction_5fpred(s: &mut Store, v316: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v317 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v316, v317) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v106, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.apply(v89, v319) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v78, v320) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v52, v321) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.apply(v35, v322) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v26, v323) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v324))
}
pub(super) fn more_191_eo__24str_5freduction_5fpred(s: &mut Store, v266: Term, v304: Term, v265: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v305 = match s.apply(v266, v304) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v305, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.apply(v265, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v160, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v141, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v310, v311) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.apply(v140, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v127, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v116, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v107, v315) { Ok(v) => v, Err(e) => return Err(e) };
more_192_eo__24str_5freduction_5fpred(s, v316, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_190_eo__24str_5freduction_5fpred(s: &mut Store, v291: Term, v292: Term, v290: Term, v287: Term, v284: Term, v5: Term, v283: Term, v266: Term, v265: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v293 = match s.construct(Constructor::eo__24emb_5fVar, &[v291, v292]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v290, v293) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v287, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v284, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.apply(v298, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v297, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v300, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v296, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v283, v303) { Ok(v) => v, Err(e) => return Err(e) };
more_191_eo__24str_5freduction_5fpred(s, v266, v304, v265, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_189_eo__24str_5freduction_5fpred(s: &mut Store, v275: Term, v280: Term, v270: Term, v267: Term, v8: Term, v5: Term, v266: Term, v265: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v281 = match s.apply(v275, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v270, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v267, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v285, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v286, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.apply(v288, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v289, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_190_eo__24str_5freduction_5fpred(s, v291, v292, v290, v287, v284, v5, v283, v266, v265, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_188_eo__24str_5freduction_5fpred(s: &mut Store, v268: Term, v8: Term, v5: Term, v267: Term, v266: Term, v265: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v269 = match s.apply(v268, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v269, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo__24emb_5fVar, &[v272, v273]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v271, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v276, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v278, v279) { Ok(v) => v, Err(e) => return Err(e) };
more_189_eo__24str_5freduction_5fpred(s, v275, v280, v270, v267, v8, v5, v266, v265, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_187_eo__24str_5freduction_5fpred(s: &mut Store, v249: Term, v256: Term, v236: Term, v226: Term, v225: Term, v207: Term, v205: Term, v171: Term, v161: Term, v8: Term, v5: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v257 = match s.apply(v249, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v236, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match eo__24eo_5ftypeof(s, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match eo__24eo_5fnil(s, v226, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v225, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v207, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v205, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v171, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v161, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_188_eo__24str_5freduction_5fpred(s, v268, v8, v5, v267, v266, v265, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_186_eo__24str_5freduction_5fpred(s: &mut Store, v244: Term, v243: Term, v240: Term, v237: Term, v8: Term, v5: Term, v236: Term, v226: Term, v225: Term, v207: Term, v205: Term, v171: Term, v161: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v245 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo__24emb_5fVar, &[v244, v245]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v243, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v240, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v237, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v250, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v251, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.construct(Constructor::eo__24emb_5fVar, &[v253, v254]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v252, v255) { Ok(v) => v, Err(e) => return Err(e) };
more_187_eo__24str_5freduction_5fpred(s, v249, v256, v236, v226, v225, v207, v205, v171, v161, v8, v5, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_185_eo__24str_5freduction_5fpred(s: &mut Store, v232: Term, v231: Term, v228: Term, v8: Term, v5: Term, v226: Term, v225: Term, v207: Term, v205: Term, v171: Term, v161: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v233 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo__24emb_5fVar, &[v232, v233]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v231, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v228, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v238, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v239, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v241, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v242, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_186_eo__24str_5freduction_5fpred(s, v244, v243, v240, v237, v8, v5, v236, v226, v225, v207, v205, v171, v161, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_184_eo__24str_5freduction_5fpred(s: &mut Store, v220: Term, v217: Term, v212: Term, v208: Term, v8: Term, v5: Term, v207: Term, v205: Term, v171: Term, v161: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v221 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v220, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v217, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v212, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v208, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v227, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v229, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v230, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_185_eo__24str_5freduction_5fpred(s, v232, v231, v228, v8, v5, v226, v225, v207, v205, v171, v161, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_183_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v208: Term, v207: Term, v205: Term, v171: Term, v161: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v209 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v209, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v210, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v211, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo__24emb_5fVar, &[v214, v215]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v213, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v218, v219) { Ok(v) => v, Err(e) => return Err(e) };
more_184_eo__24str_5freduction_5fpred(s, v220, v217, v212, v208, v8, v5, v207, v205, v171, v161, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_182_eo__24str_5freduction_5fpred(s: &mut Store, v196: Term, v8: Term, v5: Term, v195: Term, v182: Term, v172: Term, v2: Term, v171: Term, v161: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v197 = match s.apply(v196, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v197, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo__24emb_5fVar, &[v199, v200]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v198, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v195, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v182, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v172, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v206, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_183_eo__24str_5freduction_5fpred(s, v8, v5, v2, v208, v207, v205, v171, v161, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_181_eo__24str_5freduction_5fpred(s: &mut Store, v184: Term, v8: Term, v5: Term, v183: Term, v182: Term, v172: Term, v2: Term, v171: Term, v161: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v185 = match s.apply(v184, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v185, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v187, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v188, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo__24emb_5fVar, &[v190, v191]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v189, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v186, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v183, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_182_eo__24str_5freduction_5fpred(s, v196, v8, v5, v195, v182, v172, v2, v171, v161, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_180_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v172: Term, v2: Term, v171: Term, v161: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v173 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v173, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v175, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v176, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo__24emb_5fVar, &[v178, v179]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v177, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v174, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_181_eo__24str_5freduction_5fpred(s, v184, v8, v5, v183, v182, v172, v2, v171, v161, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_179_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v160: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v161 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v163, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v164, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v165, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo__24emb_5fVar, &[v167, v168]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v166, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v162, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_180_eo__24str_5freduction_5fpred(s, v8, v5, v172, v2, v171, v161, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_178_eo__24str_5freduction_5fpred(s: &mut Store, v148: Term, v8: Term, v5: Term, v147: Term, v144: Term, v143: Term, v142: Term, v2: Term, v141: Term, v140: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v149 = match s.apply(v148, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo__24emb_5fVar, &[v151, v152]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v150, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v147, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v144, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v156, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v143, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v142, v159) { Ok(v) => v, Err(e) => return Err(e) };
more_179_eo__24str_5freduction_5fpred(s, v8, v5, v2, v160, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_177_eo__24str_5freduction_5fpred(s: &mut Store, v136: Term, v5: Term, v134: Term, v129: Term, v128: Term, v8: Term, v2: Term, v127: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v137 = match s.apply(v136, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v134, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v129, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v128, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v145, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v146, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_178_eo__24str_5freduction_5fpred(s, v148, v8, v5, v147, v144, v143, v142, v2, v141, v140, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_176_eo__24str_5freduction_5fpred(s: &mut Store, v123: Term, v124: Term, v118: Term, v117: Term, v8: Term, v5: Term, v2: Term, v116: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v123, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v118, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v117, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo__24emb_5fVar, &[v131, v132]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v130, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v135, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_177_eo__24str_5freduction_5fpred(s, v136, v5, v134, v129, v128, v8, v2, v127, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_175_eo__24str_5freduction_5fpred(s: &mut Store, v109: Term, v112: Term, v108: Term, v8: Term, v5: Term, v2: Term, v107: Term, v106: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v109, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v108, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo__24emb_5fVar, &[v120, v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v119, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_176_eo__24str_5freduction_5fpred(s, v123, v124, v118, v117, v8, v5, v2, v116, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_174_eo__24str_5freduction_5fpred(s: &mut Store, v97: Term, v100: Term, v94: Term, v91: Term, v90: Term, v8: Term, v5: Term, v2: Term, v89: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v101 = match s.apply(v97, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v94, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v91, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v103, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v90, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo__24emb_5fVar, &[v110, v111]) { Ok(v) => v, Err(e) => return Err(e) };
more_175_eo__24str_5freduction_5fpred(s, v109, v112, v108, v8, v5, v2, v107, v106, v89, v78, v52, v35, v26)
}
pub(super) fn more_173_eo__24str_5freduction_5fpred(s: &mut Store, v79: Term, v88: Term, v8: Term, v5: Term, v2: Term, v78: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v79, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v98, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_174_eo__24str_5freduction_5fpred(s, v97, v100, v94, v91, v90, v8, v5, v2, v89, v78, v52, v35, v26)
}
pub(super) fn more_172_eo__24str_5freduction_5fpred(s: &mut Store, v63: Term, v76: Term, v53: Term, v8: Term, v5: Term, v2: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v63, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v53, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v82, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v83, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v80, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v86, v87) { Ok(v) => v, Err(e) => return Err(e) };
more_173_eo__24str_5freduction_5fpred(s, v79, v88, v8, v5, v2, v78, v52, v35, v26)
}
pub(super) fn more_171_eo__24str_5freduction_5fpred(s: &mut Store, v64: Term, v8: Term, v5: Term, v63: Term, v53: Term, v2: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v65 = match s.apply(v64, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v68, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v65, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v73, v75) { Ok(v) => v, Err(e) => return Err(e) };
more_172_eo__24str_5freduction_5fpred(s, v63, v76, v53, v8, v5, v2, v52, v35, v26)
}
pub(super) fn more_170_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v52: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v58, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v54, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_171_eo__24str_5freduction_5fpred(s, v64, v8, v5, v63, v53, v2, v52, v35, v26)
}
pub(super) fn more_169_eo__24str_5freduction_5fpred(s: &mut Store, v40: Term, v5: Term, v2: Term, v38: Term, v37: Term, v8: Term, v36: Term, v35: Term, v26: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v40, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v38, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v37, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v48, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v36, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_170_eo__24str_5freduction_5fpred(s, v8, v5, v2, v52, v35, v26)
}
pub(super) fn more_168_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v28: Term, v27: Term, v2: Term, v26: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v27, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_169_eo__24str_5freduction_5fpred(s, v40, v5, v2, v38, v37, v8, v36, v35, v26)
}
pub(super) fn more_167_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_168_eo__24str_5freduction_5fpred(s, v8, v5, v28, v27, v2, v26)
}
pub(super) fn case_8_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24seq_5fempty(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_167_eo__24str_5freduction_5fpred(s, v8, v5, v2, v16)
}
pub(super) fn more_220_eo__24str_5freduction_5fpred(s: &mut Store, v53: Term, v340: Term, v32: Term) -> CheckResult<Option<Term>> {
let v341 = match s.apply(v53, v340) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.apply(v32, v341) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v342))
}
pub(super) fn more_219_eo__24str_5freduction_5fpred(s: &mut Store, v328: Term, v305: Term, v303: Term, v289: Term, v281: Term, v280: Term, v251: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v329 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v328, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v305, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v303, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v289, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v281, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v334, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.apply(v280, v336) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v251, v337) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.apply(v149, v338) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v125, v339) { Ok(v) => v, Err(e) => return Err(e) };
more_220_eo__24str_5freduction_5fpred(s, v53, v340, v32)
}
pub(super) fn more_218_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v316: Term, v5: Term, v315: Term, v307: Term, v306: Term, v305: Term, v303: Term, v289: Term, v281: Term, v280: Term, v251: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v317 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v317, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v316, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v320, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v321, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v322, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v319, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v315, v325) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.apply(v307, v326) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v306, v327) { Ok(v) => v, Err(e) => return Err(e) };
more_219_eo__24str_5freduction_5fpred(s, v328, v305, v303, v289, v281, v280, v251, v149, v125, v53, v32)
}
pub(super) fn more_217_eo__24str_5freduction_5fpred(s: &mut Store, v304: Term, v2: Term, v8: Term, v5: Term, v303: Term, v289: Term, v281: Term, v280: Term, v251: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v305 = match s.apply(v304, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v308, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v310, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v311, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v312, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v309, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_218_eo__24str_5freduction_5fpred(s, v8, v316, v5, v315, v307, v306, v305, v303, v289, v281, v280, v251, v149, v125, v53, v32)
}
pub(super) fn more_216_eo__24str_5freduction_5fpred(s: &mut Store, v292: Term, v8: Term, v5: Term, v291: Term, v290: Term, v2: Term, v289: Term, v281: Term, v280: Term, v251: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v293 = match s.apply(v292, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v293, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v296, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v297, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v298, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v295, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v291, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v290, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_217_eo__24str_5freduction_5fpred(s, v304, v2, v8, v5, v303, v289, v281, v280, v251, v149, v125, v53, v32)
}
pub(super) fn more_215_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v280: Term, v251: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v281 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.apply(v284, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v285, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v286, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.apply(v283, v287) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.apply(v282, v288) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_216_eo__24str_5freduction_5fpred(s, v292, v8, v5, v291, v290, v2, v289, v281, v280, v251, v149, v125, v53, v32)
}
pub(super) fn more_214_eo__24str_5freduction_5fpred(s: &mut Store, v263: Term, v268: Term, v8: Term, v5: Term, v262: Term, v254: Term, v253: Term, v252: Term, v2: Term, v251: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v269 = match s.apply(v263, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v270, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v271, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v272, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v269, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v262, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v254, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v253, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v278, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v252, v279) { Ok(v) => v, Err(e) => return Err(e) };
more_215_eo__24str_5freduction_5fpred(s, v8, v5, v2, v280, v251, v149, v125, v53, v32)
}
pub(super) fn more_213_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v256: Term, v254: Term, v253: Term, v252: Term, v2: Term, v251: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v257 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v257, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v258, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v259, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v256, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v264, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v265, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v266, v267) { Ok(v) => v, Err(e) => return Err(e) };
more_214_eo__24str_5freduction_5fpred(s, v263, v268, v8, v5, v262, v254, v253, v252, v2, v251, v149, v125, v53, v32)
}
pub(super) fn more_212_eo__24str_5freduction_5fpred(s: &mut Store, v207: Term, v244: Term, v206: Term, v170: Term, v159: Term, v150: Term, v8: Term, v5: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v245 = match s.apply(v207, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v245, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v206, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v170, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v159, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v150, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v255, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_213_eo__24str_5freduction_5fpred(s, v8, v5, v256, v254, v253, v252, v2, v251, v149, v125, v53, v32)
}
pub(super) fn more_211_eo__24str_5freduction_5fpred(s: &mut Store, v219: Term, v232: Term, v211: Term, v210: Term, v209: Term, v5: Term, v208: Term, v207: Term, v206: Term, v170: Term, v159: Term, v150: Term, v8: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v233 = match s.apply(v219, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v211, v233) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v210, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v235, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.construct(Constructor::eo__24emb_5fVar, &[v238, v239]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v237, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v209, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v242, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v208, v243) { Ok(v) => v, Err(e) => return Err(e) };
more_212_eo__24str_5freduction_5fpred(s, v207, v244, v206, v170, v159, v150, v8, v5, v2, v149, v125, v53, v32)
}
pub(super) fn more_210_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v220: Term, v219: Term, v211: Term, v210: Term, v209: Term, v208: Term, v207: Term, v206: Term, v170: Term, v159: Term, v150: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v221 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v221, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v222, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v223, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v220, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v227, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v228, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v229, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v226, v231) { Ok(v) => v, Err(e) => return Err(e) };
more_211_eo__24str_5freduction_5fpred(s, v219, v232, v211, v210, v209, v5, v208, v207, v206, v170, v159, v150, v8, v2, v149, v125, v53, v32)
}
pub(super) fn more_209_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v208: Term, v207: Term, v206: Term, v170: Term, v159: Term, v150: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v209 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v212, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v214, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v215, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v216, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v213, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_210_eo__24str_5freduction_5fpred(s, v8, v5, v220, v219, v211, v210, v209, v208, v207, v206, v170, v159, v150, v2, v149, v125, v53, v32)
}
pub(super) fn more_208_eo__24str_5freduction_5fpred(s: &mut Store, v196: Term, v5: Term, v194: Term, v187: Term, v179: Term, v178: Term, v177: Term, v172: Term, v171: Term, v8: Term, v170: Term, v159: Term, v150: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v197 = match s.apply(v196, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v197, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v194, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v187, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v179, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v178, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v177, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v172, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v171, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_209_eo__24str_5freduction_5fpred(s, v8, v5, v208, v207, v206, v170, v159, v150, v2, v149, v125, v53, v32)
}
pub(super) fn more_207_eo__24str_5freduction_5fpred(s: &mut Store, v184: Term, v181: Term, v8: Term, v5: Term, v179: Term, v178: Term, v177: Term, v172: Term, v171: Term, v170: Term, v159: Term, v150: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v185 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v184, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v181, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v189, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v190, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v191, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v188, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v195, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_208_eo__24str_5freduction_5fpred(s, v196, v5, v194, v187, v179, v178, v177, v172, v171, v8, v170, v159, v150, v2, v149, v125, v53, v32)
}
pub(super) fn more_206_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v172: Term, v171: Term, v170: Term, v159: Term, v150: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v173 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__24emb_5fVar, &[v174, v175]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v173, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v180, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v182, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_207_eo__24str_5freduction_5fpred(s, v184, v181, v8, v5, v179, v178, v177, v172, v171, v170, v159, v150, v2, v149, v125, v53, v32)
}
pub(super) fn more_205_eo__24str_5freduction_5fpred(s: &mut Store, v160: Term, v8: Term, v5: Term, v159: Term, v150: Term, v2: Term, v149: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v161 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo__24emb_5fVar, &[v163, v164]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v162, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v166, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v161, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v160, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_206_eo__24str_5freduction_5fpred(s, v8, v5, v172, v171, v170, v159, v150, v2, v149, v125, v53, v32)
}
pub(super) fn more_204_eo__24str_5freduction_5fpred(s: &mut Store, v126: Term, v148: Term, v8: Term, v5: Term, v2: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v149 = match s.apply(v126, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo__24emb_5fVar, &[v153, v154]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v152, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v156, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v151, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_205_eo__24str_5freduction_5fpred(s, v160, v8, v5, v159, v150, v2, v149, v125, v53, v32)
}
pub(super) fn more_203_eo__24str_5freduction_5fpred(s: &mut Store, v136: Term, v133: Term, v129: Term, v128: Term, v127: Term, v8: Term, v5: Term, v126: Term, v2: Term, v125: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v137 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v136, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v133, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v129, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v128, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v127, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v144, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v145, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v142, v147) { Ok(v) => v, Err(e) => return Err(e) };
more_204_eo__24str_5freduction_5fpred(s, v126, v148, v8, v5, v2, v125, v53, v32)
}
pub(super) fn more_202_eo__24str_5freduction_5fpred(s: &mut Store, v54: Term, v124: Term, v8: Term, v5: Term, v2: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v54, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v131, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v134, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v135, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_203_eo__24str_5freduction_5fpred(s, v136, v133, v129, v128, v127, v8, v5, v126, v2, v125, v53, v32)
}
pub(super) fn more_201_eo__24str_5freduction_5fpred(s: &mut Store, v112: Term, v5: Term, v110: Term, v106: Term, v98: Term, v97: Term, v96: Term, v70: Term, v56: Term, v54: Term, v8: Term, v2: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v112, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v110, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v106, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v98, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v97, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v119, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v96, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v70, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v56, v123) { Ok(v) => v, Err(e) => return Err(e) };
more_202_eo__24str_5freduction_5fpred(s, v54, v124, v8, v5, v2, v53, v32)
}
pub(super) fn more_200_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v100: Term, v98: Term, v97: Term, v96: Term, v70: Term, v56: Term, v54: Term, v2: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v101 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v103, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v100, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_201_eo__24str_5freduction_5fpred(s, v112, v5, v110, v106, v98, v97, v96, v70, v56, v54, v8, v2, v53, v32)
}
pub(super) fn more_199_eo__24str_5freduction_5fpred(s: &mut Store, v88: Term, v8: Term, v5: Term, v87: Term, v80: Term, v72: Term, v71: Term, v70: Term, v56: Term, v54: Term, v2: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v88, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v90, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v87, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v80, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v72, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v71, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_200_eo__24str_5freduction_5fpred(s, v8, v5, v100, v98, v97, v96, v70, v56, v54, v2, v53, v32)
}
pub(super) fn more_198_eo__24str_5freduction_5fpred(s: &mut Store, v76: Term, v5: Term, v74: Term, v8: Term, v72: Term, v71: Term, v70: Term, v56: Term, v54: Term, v2: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v76, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v77, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v74, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v82, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v84, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v81, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_199_eo__24str_5freduction_5fpred(s, v88, v8, v5, v87, v80, v72, v71, v70, v56, v54, v2, v53, v32)
}
pub(super) fn more_197_eo__24str_5freduction_5fpred(s: &mut Store, v64: Term, v5: Term, v62: Term, v58: Term, v57: Term, v8: Term, v56: Term, v54: Term, v2: Term, v53: Term, v32: Term) -> CheckResult<Option<Term>> {
let v65 = match s.apply(v64, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v65, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v62, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v58, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v57, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_198_eo__24str_5freduction_5fpred(s, v76, v5, v74, v8, v72, v71, v70, v56, v54, v2, v53, v32)
}
pub(super) fn more_196_eo__24str_5freduction_5fpred(s: &mut Store, v43: Term, v52: Term, v8: Term, v5: Term, v2: Term, v32: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v43, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v60, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_197_eo__24str_5freduction_5fpred(s, v64, v5, v62, v58, v57, v8, v56, v54, v2, v53, v32)
}
pub(super) fn more_195_eo__24str_5freduction_5fpred(s: &mut Store, v40: Term, v33: Term, v8: Term, v5: Term, v2: Term, v32: Term) -> CheckResult<Option<Term>> {
let v41 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v33, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v45, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_196_eo__24str_5freduction_5fpred(s, v43, v52, v8, v5, v2, v32)
}
pub(super) fn more_194_eo__24str_5freduction_5fpred(s: &mut Store, v27: Term, v28: Term, v25: Term, v23: Term, v15: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v23, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v15, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v37, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v34, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_195_eo__24str_5freduction_5fpred(s, v40, v33, v8, v5, v2, v32)
}
pub(super) fn more_193_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v16: Term, v15: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_194_eo__24str_5freduction_5fpred(s, v27, v28, v25, v23, v15, v8, v5, v2)
}
pub(super) fn case_9_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_193_eo__24str_5freduction_5fpred(s, v8, v5, v2, v16, v15)
}
pub(super) fn more_258_eo__24str_5freduction_5fpred(s: &mut Store, v163: Term, v460: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v461 = match s.apply(v163, v460) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.apply(v150, v461) { Ok(v) => v, Err(e) => return Err(e) };
let v463 = match s.apply(v139, v462) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match s.apply(v130, v463) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.apply(v464, v465) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match s.apply(v129, v466) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match s.apply(v99, v467) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match s.apply(v88, v468) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match s.apply(v62, v469) { Ok(v) => v, Err(e) => return Err(e) };
let v471 = match s.apply(v45, v470) { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match s.apply(v36, v471) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v472))
}
pub(super) fn more_257_eo__24str_5freduction_5fpred(s: &mut Store, v428: Term, v448: Term, v426: Term, v386: Term, v376: Term, v375: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v449 = match s.apply(v428, v448) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match s.apply(v426, v449) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match s.apply(v386, v450) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match s.apply(v376, v451) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match s.apply(v452, v453) { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match s.apply(v375, v454) { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.apply(v272, v455) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match s.apply(v205, v456) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.apply(v164, v457) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.apply(v458, v459) { Ok(v) => v, Err(e) => return Err(e) };
more_258_eo__24str_5freduction_5fpred(s, v163, v460, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_256_eo__24str_5freduction_5fpred(s: &mut Store, v435: Term, v436: Term, v434: Term, v433: Term, v429: Term, v428: Term, v426: Term, v386: Term, v376: Term, v375: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v437 = match s.construct(Constructor::eo__24emb_5fVar, &[v435, v436]) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.apply(v434, v437) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.apply(v439, v440) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.apply(v441, v442) { Ok(v) => v, Err(e) => return Err(e) };
let v444 = match s.apply(v438, v443) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match s.apply(v433, v444) { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match s.apply(v429, v445) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v448 = match s.apply(v446, v447) { Ok(v) => v, Err(e) => return Err(e) };
more_257_eo__24str_5freduction_5fpred(s, v428, v448, v426, v386, v376, v375, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_255_eo__24str_5freduction_5fpred(s: &mut Store, v397: Term, v424: Term, v387: Term, v2: Term, v8: Term, v5: Term, v386: Term, v376: Term, v375: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v425 = match s.apply(v397, v424) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.apply(v387, v425) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.apply(v427, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.apply(v430, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match s.apply(v431, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.apply(v432, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_256_eo__24str_5freduction_5fpred(s, v435, v436, v434, v433, v429, v428, v426, v386, v376, v375, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_254_eo__24str_5freduction_5fpred(s: &mut Store, v411: Term, v412: Term, v410: Term, v407: Term, v398: Term, v8: Term, v5: Term, v397: Term, v387: Term, v2: Term, v386: Term, v376: Term, v375: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v413 = match s.construct(Constructor::eo__24emb_5fVar, &[v411, v412]) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.apply(v410, v413) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.apply(v407, v414) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.apply(v398, v415) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.apply(v417, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.apply(v418, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match s.construct(Constructor::eo__24emb_5fVar, &[v420, v421]) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.apply(v419, v422) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match s.apply(v416, v423) { Ok(v) => v, Err(e) => return Err(e) };
more_255_eo__24str_5freduction_5fpred(s, v397, v424, v387, v2, v8, v5, v386, v376, v375, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_253_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v400: Term, v8: Term, v398: Term, v397: Term, v387: Term, v2: Term, v386: Term, v376: Term, v375: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v401 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.apply(v401, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.apply(v403, v404) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.apply(v402, v405) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.apply(v400, v406) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.apply(v408, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.apply(v409, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_254_eo__24str_5freduction_5fpred(s, v411, v412, v410, v407, v398, v8, v5, v397, v387, v2, v386, v376, v375, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_252_eo__24str_5freduction_5fpred(s: &mut Store, v388: Term, v8: Term, v5: Term, v387: Term, v2: Term, v386: Term, v376: Term, v375: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v389 = match s.apply(v388, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.apply(v390, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.apply(v391, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.construct(Constructor::eo__24emb_5fVar, &[v393, v394]) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.apply(v392, v395) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v389, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.apply(v399, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_253_eo__24str_5freduction_5fpred(s, v5, v400, v8, v398, v397, v387, v2, v386, v376, v375, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_251_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v376: Term, v375: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v377 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.apply(v378, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.apply(v379, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.apply(v380, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.construct(Constructor::eo__24emb_5fVar, &[v382, v383]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.apply(v381, v384) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.apply(v377, v385) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_252_eo__24str_5freduction_5fpred(s, v388, v8, v5, v387, v2, v386, v376, v375, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_250_eo__24str_5freduction_5fpred(s: &mut Store, v361: Term, v364: Term, v341: Term, v5: Term, v340: Term, v339: Term, v338: Term, v293: Term, v282: Term, v273: Term, v8: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v365 = match s.apply(v361, v364) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.apply(v341, v365) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.apply(v366, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.apply(v340, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.apply(v339, v368) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.apply(v369, v370) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.apply(v338, v371) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v293, v372) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v282, v373) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.apply(v273, v374) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_251_eo__24str_5freduction_5fpred(s, v8, v5, v2, v376, v375, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_249_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v352: Term, v343: Term, v341: Term, v340: Term, v339: Term, v338: Term, v293: Term, v282: Term, v273: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v353 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.apply(v353, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.apply(v354, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.construct(Constructor::eo__24emb_5fVar, &[v356, v357]) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.apply(v355, v358) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.apply(v352, v359) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.apply(v343, v360) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.construct(Constructor::eo__24emb_5fVar, &[v362, v363]) { Ok(v) => v, Err(e) => return Err(e) };
more_250_eo__24str_5freduction_5fpred(s, v361, v364, v341, v5, v340, v339, v338, v293, v282, v273, v8, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_248_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v340: Term, v339: Term, v338: Term, v293: Term, v282: Term, v273: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v341 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v342, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.apply(v344, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v346, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.apply(v348, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.apply(v347, v350) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v345, v351) { Ok(v) => v, Err(e) => return Err(e) };
more_249_eo__24str_5freduction_5fpred(s, v8, v5, v352, v343, v341, v340, v339, v338, v293, v282, v273, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_247_eo__24str_5freduction_5fpred(s: &mut Store, v328: Term, v5: Term, v326: Term, v317: Term, v300: Term, v295: Term, v294: Term, v8: Term, v293: Term, v282: Term, v273: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v329 = match s.apply(v328, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.construct(Constructor::eo__24emb_5fVar, &[v330, v331]) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v329, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v326, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v317, v334) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v300, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.apply(v295, v336) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v294, v337) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_248_eo__24str_5freduction_5fpred(s, v8, v5, v340, v339, v338, v293, v282, v273, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_246_eo__24str_5freduction_5fpred(s: &mut Store, v301: Term, v316: Term, v8: Term, v5: Term, v300: Term, v295: Term, v294: Term, v293: Term, v282: Term, v273: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v317 = match s.apply(v301, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v318, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v320, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v322, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v321, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v319, v325) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v327, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_247_eo__24str_5freduction_5fpred(s, v328, v5, v326, v317, v300, v295, v294, v8, v293, v282, v273, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_245_eo__24str_5freduction_5fpred(s: &mut Store, v304: Term, v301: Term, v8: Term, v5: Term, v300: Term, v295: Term, v294: Term, v293: Term, v282: Term, v273: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v305 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo__24emb_5fVar, &[v306, v307]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v305, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v310, v311) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v312, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v309, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v304, v315) { Ok(v) => v, Err(e) => return Err(e) };
more_246_eo__24str_5freduction_5fpred(s, v301, v316, v8, v5, v300, v295, v294, v293, v282, v273, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_244_eo__24str_5freduction_5fpred(s: &mut Store, v283: Term, v292: Term, v8: Term, v5: Term, v282: Term, v273: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v293 = match s.apply(v283, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo__24emb_5fVar, &[v297, v298]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v296, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v302, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v303, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_245_eo__24str_5freduction_5fpred(s, v304, v301, v8, v5, v300, v295, v294, v293, v282, v273, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_243_eo__24str_5freduction_5fpred(s: &mut Store, v279: Term, v280: Term, v274: Term, v8: Term, v5: Term, v273: Term, v2: Term, v272: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v281 = match s.apply(v279, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v274, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.construct(Constructor::eo__24emb_5fVar, &[v286, v287]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.apply(v285, v288) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v289, v290) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.apply(v284, v291) { Ok(v) => v, Err(e) => return Err(e) };
more_244_eo__24str_5freduction_5fpred(s, v283, v292, v8, v5, v282, v273, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
